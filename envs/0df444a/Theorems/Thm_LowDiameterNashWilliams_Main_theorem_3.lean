-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_theorem_3
-- name    : LowDiameterNashWilliams.Main.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:41.864757+00:00
-- url     : https://prove2.me/theorems/5640231b-4a27-4667-857a-a37fc0ae67cd
-- title:
--   Theorem 3 — Frank weight splitting
-- statement:
--   Let $M_1,M_2$ be finite matroids on the same ground set $E$ whose basis families have a common member. For every integer-valued $w:E\to\mathbb Z$, there are a common basis $B$ and integer-valued $w_1,w_2$ such that
--
--   $$w=w_1+w_2,\qquad w_i(A)\le w_i(B)\quad\text{for every basis }A\text{ of }M_i,\quad i=1,2.$$
--
--   The same $B$ attains both maxima over the full individual basis families. This prior-literature dependency supplies the exact integer optimality certificate used in the extraction lemma.
--
--   Differences from the source:
--   - encoding: two finite matroids on the same ground set E → Mathlib matroids on Fin m with ground set univ and bases represented by finite sets; reason: Section 2 uses finite matroids; finite labelling changes no basis or weight function
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Theorem 3, p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Definitions.Def_LowDiameterNashWilliams_Main_Reserves
import Definitions.Def_LowDiameterNashWilliams_Main_Sampling
import Definitions.Def_LowDiameterNashWilliams_Main_Computation

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main

theorem theorem_3 :
  ∀ m : ℕ, ∀ M₁ M₂ : Matroid (Fin m), M₁.E = Set.univ → M₂.E = Set.univ →
  (∃ B : Finset (Fin m), M₁.IsBase (B : Set (Fin m)) ∧ M₂.IsBase (B : Set (Fin m))) →
  ∀ w : Fin m → ℤ, ∃ (B : Finset (Fin m)) (w₁ w₂ : Fin m → ℤ),
    M₁.IsBase (B : Set (Fin m)) ∧ M₂.IsBase (B : Set (Fin m)) ∧
    w = w₁ + w₂ ∧
    (∀ A : Finset (Fin m), M₁.IsBase (A : Set (Fin m)) → weight w₁ A ≤ weight w₁ B) ∧
    (∀ A : Finset (Fin m), M₂.IsBase (A : Set (Fin m)) → weight w₂ A ≤ weight w₂ B) := by sorry

end LowDiameterNashWilliams.Main
