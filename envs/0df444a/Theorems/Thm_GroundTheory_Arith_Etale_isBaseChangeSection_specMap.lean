-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_isBaseChangeSection_specMap
-- name    : GroundTheory.Arith.Etale.isBaseChangeSection_specMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:27:04.538827+00:00
-- url     : https://prove2.me/theorems/1cad5248-f2ae-4b93-a55b-0ae965daa38f
-- title:
--   Etale: is Base Change Section spec Map
-- statement:
--   The Etale construction uses the is Base Change Section spec Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L132-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L132-L166

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u

theorem GroundTheory.Arith.Etale.isBaseChangeSection_specMap {A R : CommRingCat.{u}} (φ : A ⟶ R) (N : (Spec A).Modules)
    [IsIso N.fromTildeΓ] : IsBaseChangeSection (Spec.map φ) N := by sorry
