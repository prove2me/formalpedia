-- Prove2me | Theorems.Thm_GlobalTheory_NormalDescent_normCoeff_map_of_isPushout
-- name    : GlobalTheory.NormalDescent.normCoeff_map_of_isPushout
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:36:29.084309+00:00
-- url     : https://prove2.me/theorems/9a885ab5-e826-4e9f-9e38-ad9de3269958
-- title:
--   Normal Descent: norm Coeff map of is Pushout
-- statement:
--   The Normal Descent construction uses the norm Coeff map of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ReversedCharpolyCoeffMapOfIsPushout.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ReversedCharpolyCoeffMapOfIsPushout.lean#L14-L34

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

theorem GlobalTheory.NormalDescent.normCoeff_map_of_isPushout {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hα : Function.Injective α) (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ) :
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by sorry
