-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_lemma_B_5
-- name    : LinearMDPRL.Linear.lemma_B_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:46:02.759927+00:00
-- url     : https://prove2.me/theorems/dfc58d86-04b0-4aea-9fdd-1fbde2d7bfae
-- title:
--   Lemma B.5 (UCB), p. 19 — on the event 𝔈, Q^k_h(x, a) ≥ Q⋆_h(x, a) for all (x, a, h, k)
-- statement:
--   Under the setting of Theorem 3.1, for an absolute constant $c_\beta>0$ as in Lemma B.4 (chosen for the constant $C\ge0$ of the event $\mathfrak E$ of Lemma B.3), on the event $\mathfrak E$ the estimates of LSVI-UCB are optimistic:
--   $$
--   Q^k_h(x,a)\ge Q^\star_h(x,a)\qquad\text{for all }(x,a,h,k)\in\mathcal S\times\mathcal A\times[H]\times[K].
--   $$
--
--   Optimism is what turns the regret into a sum of estimation errors along the trajectories actually played.
--
--   **Formalization Note.** As in Lemma B.4, $c_\beta$ is chosen after $C$; the statement is deterministic on the event, for arbitrary data.
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Lemma B.5, p. 19

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Linear_LinearMDP
import Definitions.Def_LinearMDPRL_Linear_ProofObjects

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory Matrix

/-- **Lemma B.5** (UCB; arXiv:1907.05388v2, p. 19). Under the setting of Theorem 3.1, for every
the `c_β` of Lemma B.4 (chosen for the constant `C` of the event `𝔈` of
Lemma B.3), on the event `𝔈` we have `Q^k_h(x, a) ≥ Q⋆_h(x, a)` for all `(x, a, h, k) ∈ S × A × [H] × [K]`. -/
theorem lemma_B_5 :
    ∀ C : ℝ, 0 ≤ C → ∃ cβ : ℝ, 0 < cβ ∧
      ∀ {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
        [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
      ∀ (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)), IsLinearMDP M H d φ →
      ∀ p : ℝ, 0 < p → p < 1 →
      ∀ (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A), goodEvent M φ C cβ p H K xs as →
      ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H, ∀ (x : S) (a : A),
        Qstar M H h x a ≤
          lsviQ φ M.r 1 (fun _ => cβ * d * H * Real.sqrt (iota d K H p)) H xs as k h x a := by sorry

end LinearMDPRL.Linear
