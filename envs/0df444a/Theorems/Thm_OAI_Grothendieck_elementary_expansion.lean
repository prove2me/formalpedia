-- Prove2me | Theorems.Thm_OAI_Grothendieck_elementary_expansion
-- name    : OAI.Grothendieck.elementary_expansion
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:42.930085+00:00
-- url     : https://prove2.me/theorems/dad0ce18-0cb2-434e-b084-500692a99e2c
-- statement:
--   The theorem states that, for a coherator C (a globular theory, meaning a category of shapes built from globes by iterated gluing, with morphisms preserving the globular pushouts, which has a cellular presentation as a countable-stage colimit of free extensions along admissible pairs of parallel cells and in which every admissible pair is filled by some morphism), the following holds for models of C, i.e. presheaves on C sending globular pushouts to pullbacks. Let X be a cellular model, meaning that it is built from an initial model by a well-ordered transfinite composition in which each successor step attaches cells freely along boundaries of cells of the previous stage. Let n be a natural number, let a be a map from the free model disk(n) on the n-globe to X, and let J_n : disk(n) → disk(n+1) be the map induced by the source-face inclusion of the n-globe into the (n+1)-globe. If Y, together with i : X → Y and b : disk(n+1) → Y, forms a pushout square of a and J_n, then i is a weak equivalence. Here weak equivalence means that i induces a bijection on sets of components (0-cells modulo being joined by a 1-cell) and, for every 0-cell x of X and every n, a bijection on homotopy groups, which are classes of n-loops based at the degenerate cells above x, identified when joined by an (n+1)-cell.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GrothendieckElementaryExpansion.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GrothendieckElementaryExpansion.lean; bytes 17760..18134
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GrothendieckElementaryExpansion

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

open CategoryTheory CategoryTheory.Limits

theorem elementary_expansion (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (X : C.Model) (hX : X.IsCellular) (n : ℕ)
    (a : GlobularTheory.Model.disk C n ⟶ X)
    (Y : C.Model) (i : X ⟶ Y)
    (b : GlobularTheory.Model.disk C (n + 1) ⟶ Y)
    (square : IsPushout a (GlobularTheory.Model.J C n) i b) :
    GlobularTheory.Model.WeakEquivalence hC i := by
  sorry

end Grothendieck
end OAI
