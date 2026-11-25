-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreRegular_isRadical_map_of_smooth
-- name    : GlobalTheory.FlatFibreRegular.isRadical_map_of_smooth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:41:13.426713+00:00
-- url     : https://prove2.me/theorems/ded1bf9d-6632-44d9-b3ad-52dc6a7be7d7
-- title:
--   Flat Fibre Regular: is Radical map of smooth
-- statement:
--   The Flat Fibre Regular construction uses the is Radical map of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L128-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular

theorem GlobalTheory.FlatFibreRegular.isRadical_map_of_smooth {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (𝔭 : Ideal A) [𝔭.IsPrime] : (𝔭.map (algebraMap A B)).IsRadical := by sorry
