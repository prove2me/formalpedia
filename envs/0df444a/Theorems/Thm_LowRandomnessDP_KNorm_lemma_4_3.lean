-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_lemma_4_3
-- name    : LowRandomnessDP.KNorm.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:08.48263+00:00
-- url     : https://prove2.me/theorems/ed6a561c-2fce-470f-8251-9ccace2b3886
-- title:
--   Lemma 4.3 — cell-score sensitivity and Algorithm 2 privacy
-- statement:
--   Let $K$ be admissible, $\mathcal P$ an MSSP at any positive scale, and $f:D\to\mathbb R^d$ have norm sensitivity at most one for a symmetric adjacency relation. For every fixed cell $P$,
--
--   $$|\Delta_P(f(x))-\Delta_P(f(y))|\le1\quad(x\sim y).$$
--
--   For every $\varepsilon>0$, Algorithm 2's full exponential normalizers are finite and positive, its output laws are probability measures, and the mechanism is $\varepsilon$-DP. Both the score-sensitivity and privacy clauses are retained.
--
--   Differences from the source:
--   - encoding: real vectors and their K-norm → Fin d → ℝ with the Minkowski gauge of the exact compact convex symmetric absorbing disk; reason: coordinate encoding preserves all real vectors and all source norms; compactness excludes nontrivial linear subspaces
--   - generalization: finite datasets X* → an arbitrary dataset type D with a symmetric adjacency relation; reason: specializes to D=List X with every source neighboring relation; no input measurability is imposed
--   - generalization: Section 4 uses d≥2 and a sufficiently large fixed scale from Theorem 3.2 → privacy for every positive-dimensional MSSP at every positive scale, with normalization concluded; reason: cell distance is 1-Lipschitz and MSSP counts give finite exponential sums; the Section 4 instance is included
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Lemma 4.3, PDF page 16 / printed page 14

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem lemma_4_3 {D : Type} {d : ℕ} (K : Set (Vec d)) (hK : IsBody K)
    (P : CellPartition d) (k : ℕ → ℕ) (ρ : ℝ) (hP : IsMSSP K P k ρ)
    (ε : ℝ) (hε : 0 < ε) (adj : D → D → Prop) (hadj : Std.Symm adj)
    (f : D → Vec d) (hf : SensitivityOne adj K f) :
    (∀ c : P.Cell, ∀ x y, adj x y →
      |cellDistance K P c (f x) - cellDistance K P c (f y)| ≤ 1) ∧
    (∀ x, Normalizable ε (fun c => cellDistance K P c (f x))) ∧
    (∀ x, IsProbabilityMeasure (expPart K P ε (f x))) ∧
    PureDP adj ε (fun x => expPart K P ε (f x)) := by sorry

end LowRandomnessDP.KNorm
