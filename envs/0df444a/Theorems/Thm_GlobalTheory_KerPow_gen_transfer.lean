-- Prove2me | Theorems.Thm_GlobalTheory_KerPow_gen_transfer
-- name    : GlobalTheory.KerPow.gen_transfer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:07.133737+00:00
-- url     : https://prove2.me/theorems/9d6a944b-6c35-5036-88ce-9ba0e94acff3
-- title:
--   Ker Pow: gen transfer
-- statement:
--   The Ker Pow construction uses the gen transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean#L19-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KerPow
variable {X Y Y' B B' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']

theorem GlobalTheory.KerPow.gen_transfer {M M' : LB Y} (e : M'.ι → M.ι) (hU : ∀ j, M'.U j ≤ M.U (e j))
    (hg : ∀ i j (y : Y), y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y (M'.U i ⊓ M'.U j) (M'.g i j) = gm (𝟙 Y) y (M.U (e i) ⊓ M.U (e j)) (M.g (e i) (e j)))
    (h : ∃ t : LB.Gen M, t.IsGen) : ∃ t' : LB.Gen M', t'.IsGen := by sorry
