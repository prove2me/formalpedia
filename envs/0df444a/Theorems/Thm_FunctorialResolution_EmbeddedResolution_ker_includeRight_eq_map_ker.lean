-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_includeRight_eq_map_ker
-- name    : FunctorialResolution.EmbeddedResolution.ker_includeRight_eq_map_ker
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:55.304682+00:00
-- url     : https://prove2.me/theorems/21d4e764-ab24-44bb-aa54-762c69349223
-- title:
--   Embedded Resolution: ker include Right eq map ker
-- statement:
--   The Embedded Resolution construction uses the ker include Right eq map ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/KernelFlatBaseChange.lean#L34-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/KernelFlatBaseChange.lean#L34-L69

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.ker_includeRight_eq_map_ker (R B A' : Type*) [CommRing R] [CommRing B] [CommRing A']
    [Algebra R B] [Algebra R A'] [Module.Flat R A'] :
    RingHom.ker (Algebra.TensorProduct.includeRight : A' →ₐ[R] B ⊗[R] A').toRingHom =
      (RingHom.ker (algebraMap R B)).map (algebraMap R A') := by sorry
