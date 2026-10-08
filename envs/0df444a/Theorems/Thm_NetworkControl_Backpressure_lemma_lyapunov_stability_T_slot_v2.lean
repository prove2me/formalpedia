-- Prove2me | Theorems.Thm_NetworkControl_Backpressure_lemma_lyapunov_stability_T_slot_v2
-- name    : NetworkControl.Backpressure.lemma_lyapunov_stability_T_slot_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:04.81367+00:00
-- url     : https://prove2.me/theorems/7b04bb70-f2ff-4f4d-b81e-6bd5a5ea6835
-- title:
--   Lemma 4.2 — T-slot Lyapunov drift (corrected: asymptotic limsup bound)
-- statement:
--   Let $U(t)\in\mathbb R^L_{\ge 0}$ be the backlog process of a network of $L$ queues, $L(U)=\sum_iU_i^2$, and let $T\ge 1$ be an integer such that $\mathbb E\,U_i(\tau)<\infty$ and $\mathbb E\,L(U(\tau))<\infty$ for $\tau\in\{0,\dots,T-1\}$. If there are constants $B>0$, $\varepsilon>0$ such that at every slot $t_0$ the conditional $T$-slot drift satisfies
--   $$\mathbb E\{L(U(t_0+T))-L(U(t_0))\mid U(t_0)\}\le B-\varepsilon\sum_{i=1}^LU_i(t_0)\qquad\text{a.s.},$$
--   then the network is strongly stable and
--   $$\limsup_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\sum_{i=1}^L\mathbb E\,U_i(\tau)\le\frac B\varepsilon.$$
--
--   **Formalization Note.** As in Lemma 4.1, the retired statement replaced the $\limsup$ by a bound at every $t$, which drops the initial-segment term $\sum_{\tau<T}\mathbb E\,L(U(\tau))/(\varepsilon t)$ and claims a finite-horizon bound the monograph never asserts (the accepted disproof). The corrected statement is the asymptotic bound, with the $\limsup$ in `EReal`. The initial-segment finiteness hypotheses are the monograph's; integrability of $U_i(t)$ for every $t$ is stated so that the expectations in the conclusion are not junk values. Nonnegative backlogs are the standing assumption.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Foundations and Trends in Networking 1(1), 2006, p. 52, Lemma 4.2 (T-slot Lyapunov drift)

import Mathlib
import Definitions.Def_NetworkControl_Backpressure_StronglyStable
import Definitions.Def_NetworkControl_Backpressure_lyapunovL

namespace NetworkControl.Backpressure

open MeasureTheory

/-- Lemma 4.2 (T-slot Lyapunov drift), Georgiadis–Neely–Tassiulas p. 52. Let `L(U) = Σ_i U_i²`
and let `T ≥ 1` be such that `E U_i(τ) < ∞` and `E L(U(τ)) < ∞` for `τ ∈ {0,…,T-1}`. If there
are `B > 0`, `ε > 0` such that at every slot `t0` the conditional expected `T`-slot drift satisfies
`E{L(U(t0+T)) - L(U(t0)) | U(t0)} ≤ B - ε Σ_i U_i(t0)`, then the network is strongly stable and
`limsup_{t→∞} (1/t) Σ_{τ<t} Σ_i E U_i(τ) ≤ B/ε`.

Corrected version: the second conclusion is the monograph's `limsup` bound (in `EReal`), not the
uniform-in-`t` bound of the retired version, which dropped the initial-segment term
`Σ_{τ<T} E L(U(τ))/(εt)` and claimed a finite-horizon bound the lemma never asserts. Backlogs are
nonnegative, as throughout the monograph. -/
theorem lemma_lyapunov_stability_T_slot_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {L : ℕ} (U : ℕ → Ω → Fin L → ℝ) (T : ℕ) (hT : 0 < T) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hUnn : ∀ t ω i, 0 ≤ U t ω i)
    (hMeas : ∀ t : ℕ, ∀ i : Fin L, Measurable (fun ω => U t ω i))
    (hIntegInitL : ∀ τ : ℕ, τ < T → Integrable (fun ω => lyapunovL (U τ ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin L, Integrable (fun ω => U t ω i) P)
    (hIntegDrift : ∀ t0 : ℕ,
      Integrable (fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω)) P)
    (hdrift : ∀ t0 : ℕ,
      (P[(fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω))
          | MeasurableSpace.comap (U t0) inferInstance])
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin L, U t0 ω i)) :
    NetworkStronglyStable (fun i t => ∫ ω, U t ω i ∂P) ∧
      Filter.limsup
        (fun t : ℕ =>
          (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin L, ∫ ω, U τ ω i ∂P : ℝ) : EReal))
        Filter.atTop ≤ ((B / ε : ℝ) : EReal) := by sorry

end NetworkControl.Backpressure
