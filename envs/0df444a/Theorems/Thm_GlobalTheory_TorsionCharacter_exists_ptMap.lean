-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCharacter_exists_ptMap
-- name    : GlobalTheory.TorsionCharacter.exists_ptMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:46:02.035319+00:00
-- url     : https://prove2.me/theorems/b0091ee8-8a13-4d5f-8953-e287f25e8774
-- title:
--   Torsion Character: exists pt Map
-- statement:
--   The Torsion Character construction uses the exists pt Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsAlgHomValuationSubring.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsAlgHomValuationSubring.lean#L28-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitsZpowSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCharacter
variable {O : Type} [CommRing O]

theorem GlobalTheory.TorsionCharacter.exists_ptMap {A R : Type} [CommRing A] [Algebra O A] [CommRing R] [Algebra O R]
    (c : specO O R ⟶ specO O A) : ∃ φ : A →ₐ[O] R, c = ptMap φ := by sorry
