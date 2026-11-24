-- Prove2me | Theorems.Thm_GlobalTheory_T_reversedCharpolyCoeff_map_of_isPushout
-- name    : GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:57:06.808237+00:00
-- url     : https://prove2.me/theorems/5e98e8aa-91c4-40be-b9b9-ec654f5a986e
-- title:
--   T: reversed Charpoly Coeff map of is Pushout
-- statement:
--   The T construction uses the reversed Charpoly Coeff map of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ReversedCharpolyCoeffMapOfIsPushoutStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ReversedCharpolyCoeffMapOfIsPushoutStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffMapOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffMapOfIsPushoutStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout : ∀ {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    Function.Injective α → ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ),
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by sorry
