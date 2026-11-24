-- Prove2me | Theorems.Thm_GlobalTheory_NormalDescent_reverse_map_of_injective
-- name    : GlobalTheory.NormalDescent.reverse_map_of_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:36:31.20923+00:00
-- url     : https://prove2.me/theorems/a22e3ec5-09ea-42f9-8c7e-6a80560a59fe
-- title:
--   Normal Descent: reverse map of injective
-- statement:
--   The Normal Descent construction uses the reverse map of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ReversedCharpolyCoeffMapOfIsPushout.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ReversedCharpolyCoeffMapOfIsPushout.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyMulBaseChangeFiniteMapOfIsPushoutStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCharpolyBaseChangeIntegrallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffMapOfIsPushout
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
open GlobalTheory GlobalTheory.NormalDescent

theorem GlobalTheory.NormalDescent.reverse_map_of_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by sorry
