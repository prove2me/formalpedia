-- Prove2me | Theorems.Thm_ManyServerFluid_Uniqueness_theorem_4_6
-- name    : ManyServerFluid.Uniqueness.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:44.975088+00:00
-- url     : https://prove2.me/theorems/280d2e23-56d9-47e5-8880-83b38d68f95d
-- title:
--   Theorem 4.6 — continuity of the fluid solution map: ‖ΔK̄‖_T ∨ ‖ΔD̄‖_T ≤ |ΔX̄(0)| + ‖ΔĒ‖_T when ν̄¹_0 = ν̄²_0
-- statement:
--   For $i = 1, 2$ let $(\bar X^i, \bar\nu^{(i)})$ solve the fluid equations associated with $(\bar E^i, \bar X^i(0), \bar\nu_0^{(i)}) \in \mathcal S_0$, and let $\bar K^i$, $\bar D^i$ be given by (3.8), (3.9). Write $\Delta H = H^{(2)} - H^{(1)}$. If $\bar\nu_0^1 = \bar\nu_0^2$, then for every $T < \infty$:
--   1. $$\Big[\sup_{t\in[0,T]}\Delta\bar K(t)\Big]\vee\Big[\sup_{t\in[0,T]}\Delta\bar D(t)\Big] \le \Big[|\Delta\bar X(0)| + \sup_{t\in[0,T]}\Delta\bar E(t)\Big]\vee 0; \qquad (4.8)$$
--   2. $$\|\Delta\bar K\|_T \vee \|\Delta\bar D\|_T \le |\Delta\bar X(0)| + \|\Delta\bar E\|_T; \qquad (4.9)$$
--   3. for every $f \in \mathcal C_b^1(\mathbb R_+)$,
--   $$\big\|\langle f,\bar\nu^2_s\rangle - \langle f,\bar\nu^1_s\rangle\big\|_T \le \big(2\|f\|_T + \|f'\|_T\big)\big(|\Delta\bar X(0)| + \|\Delta\bar E\|_T\big). \qquad (4.10)$$
--   Here $\|u\|_T = \sup_{s\in[0,T)}|u(s)|$.
--
--   The fluid solution is a Lipschitz function of the arrival process and of the initial number in system; with equal data it gives uniqueness of the fluid solution (Theorem 3.5).
--
--   **Formalization Note.** The printed (4.10) has $\Delta\bar X(0)$ without absolute value; with $\Delta\bar X(0) < -\|\Delta\bar E\|_T$ its right side would be negative. It is stated to follow from Lemma 4.5 and (4.9), which give $|\Delta\bar X(0)|$, so we state (4.10) with $|\Delta\bar X(0)|$. Equal initial measures are one variable $\bar\nu_0$. The suprema of the left sides are written as bounds for every $t$; the suprema of $\Delta\bar E$, $|\Delta\bar E|$, $|f|$, $|f'|$ are real suprema of bounded sets.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 54, Theorem 4.6, (4.8)–(4.10)

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
import Definitions.Def_ManyServerFluid_Uniqueness_AgeEquation
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ManyServerFluid.Uniqueness

/-- Theorem 4.6, p. 54 (continuity of the solution map): two fluid solutions with the same initial
age measure ν̄_0 satisfy (4.8), (4.9) and (4.10) for every T; ΔH = H² − H¹. (4.10) is stated with
|ΔX̄(0)| (the printed (4.10) has ΔX̄(0), a misprint: it follows from Lemma 4.5 and (4.9)). -/
theorem theorem_4_6 (S : ServiceLaw) (E₁ E₂ : ℝ → ℝ) (X0₁ X0₂ : ℝ) (ν0 : FiniteMeasure ℝ)
    (X₁ X₂ : ℝ → ℝ) (ν₁ ν₂ : ℝ → FiniteMeasure ℝ)
    (h0₁ : S.InS0 E₁ X0₁ ν0) (h0₂ : S.InS0 E₂ X0₂ ν0)
    (hs₁ : S.IsFluidSolution E₁ X0₁ ν0 X₁ ν₁) (hs₂ : S.IsFluidSolution E₂ X0₂ ν0 X₂ ν₂)
    (T : ℝ) :
    -- (4.8)
    (∀ t ∈ Icc 0 T,
        S.Kbar ν₂ t - S.Kbar ν₁ t ≤
          max (|X0₂ - X0₁| + sSup ((fun s => E₂ s - E₁ s) '' Icc 0 T)) 0 ∧
        S.Dbar ν₂ t - S.Dbar ν₁ t ≤
          max (|X0₂ - X0₁| + sSup ((fun s => E₂ s - E₁ s) '' Icc 0 T)) 0) ∧
    -- (4.9)
    (∀ t ∈ Ico 0 T,
        |S.Kbar ν₂ t - S.Kbar ν₁ t| ≤ |X0₂ - X0₁| + sSup ((fun s => |E₂ s - E₁ s|) '' Ico 0 T) ∧
        |S.Dbar ν₂ t - S.Dbar ν₁ t| ≤ |X0₂ - X0₁| + sSup ((fun s => |E₂ s - E₁ s|) '' Ico 0 T)) ∧
    -- (4.10), with |ΔX̄(0)|
    (∀ f : ℝ → ℝ, IsCb1 f → ∀ t ∈ Ico 0 T,
        |∫ x, f x ∂(ν₂ t : Measure ℝ) - ∫ x, f x ∂(ν₁ t : Measure ℝ)| ≤
          (2 * sSup ((fun s => |f s|) '' Ico 0 T) + sSup ((fun s => |deriv f s|) '' Ico 0 T)) *
            (|X0₂ - X0₁| + sSup ((fun s => |E₂ s - E₁ s|) '' Ico 0 T))) := by sorry

end ManyServerFluid.Uniqueness
