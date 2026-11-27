-- Prove2me | Theorems.Thm_GlobalTheory_ValueTwoGen_exists_unit_gen
-- name    : GlobalTheory.ValueTwoGen.exists_unit_gen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:02.10462+00:00
-- url     : https://prove2.me/theorems/6d85bacd-89e3-5b3d-bf13-35095dc1ff2d
-- title:
--   Value Two Gen: exists unit gen
-- statement:
--   The Value Two Gen construction uses the exists unit gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsValueAtEqUnitMul.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsValueAtEqUnitMul.lean#L17-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IntegralSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsValueAtEqUnitMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ModelMetric
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.ValueTwoGen

theorem GlobalTheory.ValueTwoGen.exists_unit_gen {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (t t' : LB.Gen M) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, (t'.s j).val =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom (w : Γ(Y, ⊤)) * (t.s j).val := by sorry
