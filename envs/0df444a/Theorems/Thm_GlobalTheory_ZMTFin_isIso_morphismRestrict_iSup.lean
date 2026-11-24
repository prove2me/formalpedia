-- Prove2me | Theorems.Thm_GlobalTheory_ZMTFin_isIso_morphismRestrict_iSup
-- name    : GlobalTheory.ZMTFin.isIso_morphismRestrict_iSup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:48.929264+00:00
-- url     : https://prove2.me/theorems/18b6421c-adb2-4440-b887-77dc63633621
-- title:
--   ZMTFin: is Iso morphism Restrict i Sup
-- statement:
--   The ZMTFin construction uses the is Iso morphism Restrict i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCompOpenImmersionOfQuasiFinite.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCompOpenImmersionOfQuasiFinite.lean#L39-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCoequifiberedSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCompOpenImmersionOfQuasiFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
open GlobalTheory GlobalTheory.ZMTFin

theorem GlobalTheory.ZMTFin.isIso_morphismRestrict_iSup {Z T : Scheme.{0}} (g : Z ⟶ T) {ι : Type} (W : ι → T.Opens)
    (hW : ∀ i, IsIso (g ∣_ W i)) : IsIso (g ∣_ ⨆ i, W i) := by sorry
