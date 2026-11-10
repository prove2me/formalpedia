-- Prove2me | Theorems.Thm_OptStochMatch_Tight_lemma_4_4
-- name    : OptStochMatch.Tight.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:57:54.381555+00:00
-- url     : https://prove2.me/theorems/f52dd29c-53eb-4564-a514-30a9b6e0688e
-- title:
--   Lemma 4.4 — generator of the online process applied to the potential f_i
-- statement:
--   Under the posterior allocation policy (4.1), with $f_i(t,X_t)=x_i(t)+1\{x_i(t)<Z_i\}q(t,x_i(t))$ (4.7) and the generator $L$ of (4.8): while job $i$ is unfinished, with $h=x_i(t)$, $(Lf_i)(t,X_t)=\partial_tq(t,h)+s_i(t)\big(1+\partial_hq(t,h)-q(t,h)\big)$ (4.10); after job $i$ completes, $(Lf_i)(t,X_t)=0$.
--
--   Differences from the source:
--   - encoding: the posterior allocation policy (4.1) → any SchedPolicy whose rate equals (4.1) after every completion history with nonnegative accumulated work (FollowsPosterior); reason: this gives a feedback-rule extension to all nonnegative states, including every reachable state; negative-work states are irrelevant to the source process
--   - reading: (Lf)(t,x) = lim_{δ→0+} (E[f(t+δ, X_{t+δ}) | X_t = x] − f(t,x))/δ → for 0 ≤ t < 1 and every sequence δ_k > 0 tending to 0: (E[f_i(t+δ_k, ·) | F_t] − f_i(t, ·))/δ_k converges almost surely to the stated value; reason: the state X_t is Markov under (4.1) (p. 15–16), so conditioning on X_t and on the history F_t agree; conditional expectations are a.e.-defined, so the right limit is taken along sequences; the forward limit needs t < 1
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Lemma 4.4, eq. (4.10), p. 16 (PDF p. 17), with (4.7)–(4.8)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Laws
import Definitions.Def_OptStochMatch_Tight_Scheduling
import Definitions.Def_OptStochMatch_Tight_Comparison
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace OptStochMatch.Tight

/-- Lemma 4.4 (p. 16, PDF 17). Under the posterior allocation policy (4.1), let
`f_i(t, X_t) = x_i(t) + 1{x_i(t) < Z_i} q(t, x_i(t))` (4.7) and let `L` be the generator (4.8),
the right derivative in time of the conditional expectation of `f_i(t + δ, X_{t+δ})` given the
history at time `t`. For `0 ≤ t < 1`, while job `i` is unfinished, with `h = x_i(t)`,
`(L f_i)(t, X_t) = ∂_t q(t, h) + s_i(t)(1 + ∂_h q(t, h) − q(t, h))` (4.10); after job `i`
completes, `(L f_i)(t, X_t) = 0`. The limit `δ → 0+` is taken along every sequence `δ_k ↓ 0`,
almost surely. -/
theorem lemma_4_4 {m : ℕ} (P : Set (Fin m → ℝ)) (hP : IsRateRegion P)
    (Y : (Fin m → ℝ) → (Fin m → ℝ)) (hY : IsOfflineAllocation P Y)
    (σ : SchedPolicy m P) (hσ : FollowsPosterior Y σ) (u : ℝ) (i : Fin m)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (δ : ℕ → ℝ) (hδpos : ∀ k, 0 < δ k) (hδ : Tendsto δ atTop (𝓝 0)) :
    let f : ℝ → (Fin m → ℝ) → ℝ := fun v z =>
      workProc σ u z v i + (if workProc σ u z v i < z i then qComp v (workProc σ u z v i) else 0)
    let D : ℕ → (Fin m → ℝ) → ℝ := fun k z =>
      (condExp (obsAlgebra σ u t) (demandLaw m) (f (t + δ k)) z - f t z) / δ k
    (∀ᵐ z ∂(demandLaw m), workProc σ u z t i < z i →
      Tendsto (fun k => D k z) atTop
        (𝓝 (deriv (fun t' => qComp t' (workProc σ u z t i)) t +
          rateProc σ u z t i *
            (1 + deriv (fun h' => qComp t h') (workProc σ u z t i) -
              qComp t (workProc σ u z t i))))) ∧
    (∀ᵐ z ∂(demandLaw m), ¬ workProc σ u z t i < z i →
      Tendsto (fun k => D k z) atTop (𝓝 0)) := by sorry

end OptStochMatch.Tight
