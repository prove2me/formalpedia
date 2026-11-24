-- Prove2me | Theorems.Thm_GlobalTheory_T_charpolyMulBaseChangeFinite_map_of_isPushout
-- name    : GlobalTheory.T.charpolyMulBaseChangeFinite_map_of_isPushout
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:47.111324+00:00
-- url     : https://prove2.me/theorems/cff69bad-dfcd-4457-9386-2bdcd0834ee7
-- title:
--   T: charpoly Mul Base Change Finite map of is Pushout
-- statement:
--   The T construction uses the charpoly Mul Base Change Finite map of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyMulBaseChangeFiniteMapOfIsPushoutStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyMulBaseChangeFiniteMapOfIsPushoutStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyMulBaseChangeFiniteMapOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyMulBaseChangeFiniteMapOfIsPushoutStatement
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

theorem GlobalTheory.T.charpolyMulBaseChangeFinite_map_of_isPushout : ∀ {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field K']
    [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K'), (∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) →
    ∀ b : B, charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by sorry
