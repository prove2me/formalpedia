-- Prove2me | Theorems.Thm_NetworkControl_Backpressure_lemma_lyapunov_stability_v2
-- name    : NetworkControl.Backpressure.lemma_lyapunov_stability_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:18.037165+00:00
-- url     : https://prove2.me/theorems/aa415b8e-8c65-4749-b733-6177f7571659
-- title:
--   Lemma 4.1 — Lyapunov stability (corrected: asymptotic limsup bound, not a uniform bound)
-- statement:
--   Let $U(t)\in\mathbb R^L_{\ge 0}$ be the backlog process of a network of $L$ queues on a probability space, $L(U)=\sum_iU_i^2$ the quadratic Lyapunov function, and suppose $\mathbb E\,L(U(0))<\infty$. If there are constants $B>0$, $\varepsilon>0$ such that at every slot $t$
--   $$\mathbb E\{L(U(t+1))-L(U(t))\mid U(t)\}\le B-\varepsilon\sum_{i=1}^LU_i(t)\qquad\text{a.s.},$$
--   then the network is strongly stable (every queue has a bounded time-average expected backlog) and
--   $$\limsup_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\sum_{i=1}^L\mathbb E\,U_i(\tau)\le\frac B\varepsilon.$$
--
--   **Formalization Note.** The retired statement replaced the $\limsup$ bound by the uniform bound "for all $t$, $\frac1t\sum_{\tau<t}\sum_i\mathbb E\,U_i(\tau)\le B/\varepsilon$", which drops the initial-condition term $\mathbb E\,L(U(0))/(\varepsilon t)$ of the telescoped drift inequality and is strictly stronger than the lemma (the accepted disproof). The corrected statement is the monograph's asymptotic bound; the $\limsup$ is taken in `EReal` so that it is never a junk value. $\mathbb E\,L(U(0))<\infty$ and nonnegative backlogs are the monograph's standing hypotheses. Strong stability is `NetworkStronglyStable` (Definition 3.2, each queue in the bounded-Cesàro-average form of Definition 3.1).
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Foundations and Trends in Networking 1(1), 2006, p. 50, Lemma 4.1 (Lyapunov Stability), with L(U) defined on p. 49

import Mathlib
import Definitions.Def_NetworkControl_Backpressure_StronglyStable
import Definitions.Def_NetworkControl_Backpressure_lyapunovL

namespace NetworkControl.Backpressure

open MeasureTheory

/-- Lemma 4.1 (Lyapunov Stability), Georgiadis–Neely–Tassiulas p. 50. Let `L(U) = Σ_i U_i²` with
`E L(U(0)) < ∞`. If there are constants `B > 0`, `ε > 0` such that at every slot `t` the
conditional expected drift satisfies `E{L(U(t+1)) - L(U(t)) | U(t)} ≤ B - ε Σ_i U_i(t)`, then
the network is strongly stable and `limsup_{t→∞} (1/t) Σ_{τ<t} Σ_i E U_i(τ) ≤ B/ε`.

Corrected version: the second conclusion is the monograph's `limsup` bound (read in `EReal`,
where `Filter.limsup` never returns a junk value), not the uniform-in-`t` bound of the retired
version, which silently dropped the initial-condition term `E L(U(0))/(εt)` and claimed more than
the lemma asserts. The hypothesis `E L(U(0)) < ∞` and the nonnegativity of backlogs are the
monograph's standing assumptions. -/
theorem lemma_lyapunov_stability_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {L : ℕ} (U : ℕ → Ω → Fin L → ℝ) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hUnn : ∀ t ω i, 0 ≤ U t ω i)
    (hMeas : ∀ t : ℕ, ∀ i : Fin L, Measurable (fun ω => U t ω i))
    (hIntegL0 : Integrable (fun ω => lyapunovL (U 0 ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin L, Integrable (fun ω => U t ω i) P)
    (hIntegDrift : ∀ t : ℕ, Integrable (fun ω => lyapunovL (U (t + 1) ω) - lyapunovL (U t ω)) P)
    (hdrift : ∀ t : ℕ,
      (P[(fun ω => lyapunovL (U (t + 1) ω) - lyapunovL (U t ω))
          | MeasurableSpace.comap (U t) inferInstance])
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin L, U t ω i)) :
    NetworkStronglyStable (fun i t => ∫ ω, U t ω i ∂P) ∧
      Filter.limsup
        (fun t : ℕ =>
          (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin L, ∫ ω, U τ ω i ∂P : ℝ) : EReal))
        Filter.atTop ≤ ((B / ε : ℝ) : EReal) := by sorry

end NetworkControl.Backpressure
