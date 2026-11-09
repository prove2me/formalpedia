-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_lemma_3_1
-- name    : LowRandomnessDP.KNorm.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:58.321064+00:00
-- url     : https://prove2.me/theorems/43f41e05-a6a9-4136-bb6a-02abf7f9ed9e
-- title:
--   Lemma 3.1 — normalized-body MSSP existence
-- statement:
--   There is an absolute $C>0$ such that for every positive dimension $d$, every admissible body with $B_2^d(1)\subseteq K\subseteq B_2^d(\sqrt d)$, and every scale $\rho>0$, there is one countable $(k_d,\rho)$-MSSP satisfying
--
--   $$k_d(\ell)\le C d\log(d+1)e^{d/\ell},\qquad1\le\ell\le d.$$
--
--   All reciprocal scales use the same partition and representatives. This is the normalized geometric existence target.
--
--   Differences from the source:
--   - encoding: real vectors and their K-norm → Fin d → ℝ with the Minkowski gauge of the exact compact convex symmetric absorbing disk; reason: coordinate encoding preserves all real vectors and all source norms; compactness excludes nontrivial linear subspaces
--   - encoding: O(d log d exp(d/ℓ)) for every positive dimension → one uniform C d log(d+1) exp(d/ℓ) bound; reason: PDF 9–10, printed 7–8, explicitly uses λ=C d log(d+1) and 6C in the proof; this includes d=1 without a zero bound
--   - encoding: an MSSP, with the scale omitted → existence at every positive scale with countably many cells; reason: rescaling is explicitly allowed by footnote 3 and the proof constructs a countable periodic partition
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Lemma 3.1, PDF page 9 / printed page 7

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem lemma_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 0 < d → ∀ K : Set (Vec d), IsBody K →
      euclideanBall d 1 ⊆ K → K ⊆ euclideanBall d (Real.sqrt d) →
      ∀ ρ : ℝ, 0 < ρ → ∃ (P : CellPartition d) (k : ℕ → ℕ),
        IsMSSP K P k ρ ∧ RateBound C d k ∧ P.cells.Countable := by sorry

end LowRandomnessDP.KNorm
