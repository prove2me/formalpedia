-- Prove2me | Theorems.Thm_ManyServerFluid_Uniqueness_lemma_4_5
-- name    : ManyServerFluid.Uniqueness.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:36.158362+00:00
-- url     : https://prove2.me/theorems/f15821f2-3892-464c-a29c-4f6558274564
-- title:
--   Lemma 4.5 — ‖⟨f, ν̄²⟩ − ⟨f, ν̄¹⟩‖_T ≤ ‖f‖_M |Δυ_0|_TV + (2‖f‖_T + ‖f′‖_T)‖ΔZ‖_T
-- statement:
--   For $i = 1, 2$ let $\upsilon_0^i \in \mathcal M[0,M)$ and $Z^i \in BV_0[0,\infty)$, and let $\bar\nu^i \in \mathcal D_{\mathcal M[0,M)}[0,\infty)$ satisfy the bound (4.1) and the age equation (4.2) for $\upsilon_0^i$ and $Z^i$. Write $\Delta Z = Z^2 - Z^1$ and $\Delta\upsilon_0 = \upsilon_0^{(2)} - \upsilon_0^{(1)}$. Then for every $T < \infty$ and $f \in \mathcal C_b^1(\mathbb R_+)$
--   $$\big\|\langle f,\bar\nu^2_s\rangle - \langle f,\bar\nu^1_s\rangle\big\|_T \le \|f\|_M\,|\Delta\upsilon_0|_{TV} + \big(2\|f\|_T + \|f'\|_T\big)\,\|\Delta Z\|_T, \qquad (4.7)$$
--   where $\|u\|_T = \sup_{s\in[0,T)}|u(s)|$, $\|f\|_M = \sup_{x\in[0,M)}|f(x)|$ and $|\Delta\upsilon_0|_{TV}$ is the total variation of $\Delta\upsilon_0$ on $[0,M)$.
--
--   The solution of the age equation therefore depends Lipschitz-continuously on its data, in total variation for the initial measure and in the supremum norm for the input $Z$; this is the analytic core of the continuity of the fluid solution map.
--
--   **Formalization Note.** All norms and the right-hand side are computed in $[0,\infty]$, since $|\Delta\upsilon_0|_{TV}$ may be infinite (then the bound is trivial unless $f = 0$ on $[0,M)$), with $0\cdot\infty = 0$. $Z^i = Z^i_+ - Z^i_-$ with $Z^i_\pm \in \mathcal I_0$.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 53, Lemma 4.5, (4.7)

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
import Definitions.Def_ManyServerFluid_Uniqueness_AgeEquation
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ManyServerFluid.Uniqueness

/-- Lemma 4.5, (4.7), p. 53: for i = 1, 2 let ν^i satisfy (4.1) and the age equation (4.2) for
υ_0^i ∈ M[0, M) and Z^i = Z^i₊ − Z^i₋ ∈ BV_0[0, ∞). Then for every T and f ∈ C_b^1(R₊),
‖⟨f, ν²_s⟩ − ⟨f, ν¹_s⟩‖_T ≤ ‖f‖_M |Δυ_0|_TV + (2‖f‖_T + ‖f′‖_T) ‖ΔZ‖_T,
with ‖·‖_T the supremum over [0, T), ‖f‖_M the supremum over [0, M), all in [0, ∞]. -/
theorem lemma_4_5 (S : ServiceLaw) (ν₁ ν₂ : ℝ → Measure ℝ) (υ₁ υ₂ : Measure ℝ)
    (Z1p Z1m Z2p Z2m : ℝ → ℝ)
    (hν₁ : S.IsVagueCadlag ν₁) (hν₂ : S.IsVagueCadlag ν₂)
    (hh₁ : S.HazardBound ν₁) (hh₂ : S.HazardBound ν₂)
    (hυ₁ : S.IsRadonAges υ₁) (hυ₂ : S.IsRadonAges υ₂)
    (hZ1p : ServiceLaw.IsI0 Z1p) (hZ1m : ServiceLaw.IsI0 Z1m)
    (hZ2p : ServiceLaw.IsI0 Z2p) (hZ2m : ServiceLaw.IsI0 Z2m)
    (hage₁ : S.AgeEq υ₁ Z1p Z1m ν₁) (hage₂ : S.AgeEq υ₂ Z2p Z2m ν₂)
    (T : ℝ) (f : ℝ → ℝ) (hf : IsCb1 f) :
    (⨆ s ∈ Ico 0 T, ENNReal.ofReal |∫ x, f x ∂(ν₂ s) - ∫ x, f x ∂(ν₁ s)|) ≤
      (⨆ x ∈ S.Ages, ENNReal.ofReal |f x|) * S.tvDiff υ₁ υ₂
      + (2 * (⨆ s ∈ Ico 0 T, ENNReal.ofReal |f s|)
          + ⨆ s ∈ Ico 0 T, ENNReal.ofReal |deriv f s|)
        * ⨆ s ∈ Ico 0 T, ENNReal.ofReal |(Z2p s - Z2m s) - (Z1p s - Z1m s)| := by sorry

end ManyServerFluid.Uniqueness
