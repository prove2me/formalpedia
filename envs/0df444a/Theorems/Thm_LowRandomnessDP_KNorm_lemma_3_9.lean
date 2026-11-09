-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_lemma_3_9
-- name    : LowRandomnessDP.KNorm.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:15.608026+00:00
-- url     : https://prove2.me/theorems/24d8270c-a46b-448d-a2ed-6ebccf7fdcf1
-- title:
--   Lemma 3.9 — distant MSSP cell counts
-- statement:
--   For an MSSP in any admissible $K$-norm, every $y\in\mathbb R^d$ and every $\gamma\ge1$ satisfy
--
--   $$|\mathcal P_{<\gamma}(y)|\le k_d(1)(3\gamma)^d.$$
--
--   The scale is any positive $\rho$ and the collection uses the strict infimal-distance threshold. This is the large-radius cell-count target.
--
--   Differences from the source:
--   - encoding: real vectors and their K-norm → Fin d → ℝ with the Minkowski gauge of the exact compact convex symmetric absorbing disk; reason: coordinate encoding preserves all real vectors and all source norms; compactness excludes nontrivial linear subspaces
--   - encoding: cardinality of a cell collection → a bound on the cardinality of every finite subset; reason: equivalent to the finite cardinal bound and cannot assign zero to an infinite set
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Lemma 3.9, PDF page 14 / printed page 12

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem lemma_3_9 {d : ℕ} (K : Set (Vec d)) (hK : IsBody K)
    (P : CellPartition d) (k : ℕ → ℕ) (ρ : ℝ) (hP : IsMSSP K P k ρ)
    (y : Vec d) (γ : ℝ) (hγ : 1 ≤ γ) :
    CountLe (nearCells K P ρ γ y) ((k 1 : ℝ) * (3 * γ) ^ d) := by sorry

end LowRandomnessDP.KNorm
