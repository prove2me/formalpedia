-- Prove2me | Theorems.Thm_GlobalTheory_NormalDescent_charK_map_of_isPushout
-- name    : GlobalTheory.NormalDescent.charK_map_of_isPushout
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:36:42.502448+00:00
-- url     : https://prove2.me/theorems/105d1842-bf57-48d5-9828-0cc22356a03c
-- title:
--   Normal Descent: char K map of is Pushout
-- statement:
--   The Normal Descent construction uses the char K map of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyMulBaseChangeFiniteMapOfIsPushout.lean#L9-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CharpolyMulBaseChangeFiniteMapOfIsPushout.lean#L9-L47

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyMulBaseChangeFiniteMapOfIsPushout
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NormalDescent
open CategoryTheory Polynomial TensorProduct

theorem GlobalTheory.NormalDescent.charK_map_of_isPushout {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Field K] [Field K'] [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B')
    (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K')
    (hι : ∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) (b : B) :
    charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by sorry
