-- Prove2me | Theorems.Thm_GlobalTheory_ZH_FibPre_compat_iff
-- name    : GlobalTheory.ZH.FibPre.compat_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:42.228867+00:00
-- url     : https://prove2.me/theorems/e87e3214-f8c5-4de7-b63c-74fff118209d
-- title:
--   Fib Pre: compat iff
-- statement:
--   The Fib Pre construction uses the compat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOfWeightEq.lean#L38-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOfWeightEq.lean#L38-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOfWeightEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ZH

theorem GlobalTheory.ZH.FibPre.compat_iff {k : Type} [Field k] (Φ : FibPre k) (t : ∀ l, Γ(Φ.E.B.left, Φ.N₀.U l))
    (i j : Φ.N₀.ι) :
    ((Φ.G.left.presheaf.map (homOfLE (inf_le_left : (Φ.H 1).U i ⊓ (Φ.H 1).U j ≤ (Φ.H 1).U i)).op).hom
        ((Φ.D.q.left.app (Φ.N₀.U i)).hom (t i)) =
      ((Φ.H 1).g i j : Γ(Φ.G.left, (Φ.H 1).U i ⊓ (Φ.H 1).U j)) *
        (Φ.G.left.presheaf.map (homOfLE (inf_le_right : (Φ.H 1).U i ⊓ (Φ.H 1).U j ≤ (Φ.H 1).U j)).op).hom
          ((Φ.D.q.left.app (Φ.N₀.U j)).hom (t j))) ↔
    (Φ.E.B.left.presheaf.map (homOfLE (inf_le_left : Φ.N₀.U i ⊓ Φ.N₀.U j ≤ Φ.N₀.U i)).op).hom (t i) =
      (Φ.N₀.g i j : Γ(Φ.E.B.left, Φ.N₀.U i ⊓ Φ.N₀.U j)) *
        (Φ.E.B.left.presheaf.map (homOfLE (inf_le_right : Φ.N₀.U i ⊓ Φ.N₀.U j ≤ Φ.N₀.U j)).op).hom (t j) := by sorry
