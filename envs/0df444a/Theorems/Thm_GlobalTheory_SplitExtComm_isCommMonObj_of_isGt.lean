-- Prove2me | Theorems.Thm_GlobalTheory_SplitExtComm_isCommMonObj_of_isGt
-- name    : GlobalTheory.SplitExtComm.isCommMonObj_of_isGt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:54:47.464416+00:00
-- url     : https://prove2.me/theorems/dc254d3d-ffb2-4c33-a5fd-cb94de6771da
-- title:
--   Split Ext Comm: is Comm Mon Obj of is Gt
-- statement:
--   The Split Ext Comm construction uses the is Comm Mon Obj of is Gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsCommMonObjOfDominant.lean#L30-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsCommMonObjOfDominant.lean#L30-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyTorusExtensionOfIsGt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsCommMonObjOfDominant
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitExtComm

theorem GlobalTheory.SplitExtComm.isCommMonObj_of_isGt {O C : Type} [CommRing O] [Field C] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C)) (E : SplitExt (Spec (CommRingCat.of O)))
    (G : Over (Spec (CommRingCat.of O))) [GrpObj G] (h : E.IsGt G) : IsCommMonObj G := by sorry
