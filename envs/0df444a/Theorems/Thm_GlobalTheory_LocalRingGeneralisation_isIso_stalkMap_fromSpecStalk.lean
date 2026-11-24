-- Prove2me | Theorems.Thm_GlobalTheory_LocalRingGeneralisation_isIso_stalkMap_fromSpecStalk
-- name    : GlobalTheory.LocalRingGeneralisation.isIso_stalkMap_fromSpecStalk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:18:51.090797+00:00
-- url     : https://prove2.me/theorems/6e10cf68-6159-47db-aa01-eaebc3d46f00
-- title:
--   Local Ring Generalisation: is Iso stalk Map from Spec Stalk
-- statement:
--   The Local Ring Generalisation construction uses the is Iso stalk Map from Spec Stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/StalkGenerizationGermCompat.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/StalkGenerizationGermCompat.lean#L20-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_StalkGenerizationGermCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open GlobalTheory GlobalTheory.LocalRingGeneralisation

theorem GlobalTheory.LocalRingGeneralisation.isIso_stalkMap_fromSpecStalk (X : Scheme.{0}) (x : X) (y : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap y) := by sorry
