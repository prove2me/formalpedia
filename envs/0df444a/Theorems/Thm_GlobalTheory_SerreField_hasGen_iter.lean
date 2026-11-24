-- Prove2me | Theorems.Thm_GlobalTheory_SerreField_hasGen_iter
-- name    : GlobalTheory.SerreField.hasGen_iter
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:52.10682+00:00
-- url     : https://prove2.me/theorems/a7a79780-bde4-4ed8-bbe2-7d0bbf06d265
-- title:
--   Serre Field: has Gen iter
-- statement:
--   The Serre Field construction uses the has Gen iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsOddNeZero.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsOddNeZero.lean#L83-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulPullOfCubeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsOddNeZero
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SerreField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.MulPull
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
variable {A}
omit [GrpObj A] [IsCommMonObj A]

theorem GlobalTheory.SerreField.hasGen_iter {L : LB A.left} (hL : L.IsLB) (σ : A ≅ A)
    (h : HasGen L (K := Fin 2) ![σ.hom.left, 𝟙 A.left] ![1, -1]) (m : ℕ) :
    HasGen L (K := Fin 2) ![(iter σ m).hom.left, 𝟙 A.left] ![1, -1] := by sorry
