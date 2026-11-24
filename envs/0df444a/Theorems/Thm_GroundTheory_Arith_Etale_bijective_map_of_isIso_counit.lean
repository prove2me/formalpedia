-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_bijective_map_of_isIso_counit
-- name    : GroundTheory.Arith.Etale.bijective_map_of_isIso_counit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:26:59.654609+00:00
-- url     : https://prove2.me/theorems/8ee38c91-edfe-4e71-b95b-ea8743473c7b
-- title:
--   Etale: bijective map of is Iso counit
-- statement:
--   The Etale construction uses the bijective map of is Iso counit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L62-L72

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

theorem GroundTheory.Arith.Etale.bijective_map_of_isIso_counit {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (X Y : D) [IsIso (adj.counit.app X)] :
    Function.Bijective (fun h : X ⟶ Y => G.map h) := by sorry
