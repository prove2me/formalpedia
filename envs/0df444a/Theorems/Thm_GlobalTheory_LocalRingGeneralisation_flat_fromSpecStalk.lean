-- Prove2me | Theorems.Thm_GlobalTheory_LocalRingGeneralisation_flat_fromSpecStalk
-- name    : GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:18:55.133946+00:00
-- url     : https://prove2.me/theorems/0d7d854e-4e7c-46bf-abea-4903156cd2f0
-- title:
--   Local Ring Generalisation: flat from Spec Stalk
-- statement:
--   The Local Ring Generalisation construction uses the flat from Spec Stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/StalkGenerizationGermCompat.lean#L6-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/StalkGenerizationGermCompat.lean#L6-L18

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

theorem GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk (X : Scheme.{0}) (x : X) : Flat (X.fromSpecStalk x) := by sorry
