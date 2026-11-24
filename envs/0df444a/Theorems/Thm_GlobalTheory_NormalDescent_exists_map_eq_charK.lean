-- Prove2me | Theorems.Thm_GlobalTheory_NormalDescent_exists_map_eq_charK
-- name    : GlobalTheory.NormalDescent.exists_map_eq_charK
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:55.41235+00:00
-- url     : https://prove2.me/theorems/e49f8d70-63b2-46f8-89d3-64f611dd26ae
-- title:
--   Normal Descent: exists map eq char K
-- statement:
--   The Normal Descent construction uses the exists map eq char K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCharpolyBaseChangeIntegrallyClosed.lean#L8-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCharpolyBaseChangeIntegrallyClosed.lean#L8-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCharpolyBaseChangeIntegrallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent TensorProduct
open GlobalTheory GlobalTheory.NormalDescent

theorem GlobalTheory.NormalDescent.exists_map_eq_charK : ∀ {A B K : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K]
    [Algebra A K] [IsFractionRing A K] (φ : A →+* B) (hφ : φ.Finite) (b : B),
    ∃ P : A[X], P.map (algebraMap A K) = charK φ hφ K b := by sorry
