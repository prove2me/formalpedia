-- Prove2me | Theorems.Thm_GlobalTheory_StabFlat_height_of_etale_mvPolynomial
-- name    : GlobalTheory.StabFlat.height_of_etale_mvPolynomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:53.984799+00:00
-- url     : https://prove2.me/theorems/7d79b8e6-87cc-47fa-a9c4-f6e7d4ea02fd
-- title:
--   Stab Flat: height of etale mv Polynomial
-- statement:
--   The Stab Flat construction uses the height of etale mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocalizationOfIsStandardSmooth.lean#L73-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocalizationOfIsStandardSmooth.lean#L73-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocalizationOfIsStandardSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.StabFlat

theorem GlobalTheory.StabFlat.height_of_etale_mvPolynomial (K B : Type*) [Field K] [CommRing B] (g : ℕ)
    [Algebra (MvPolynomial (Fin g) K) B] [Algebra.Etale (MvPolynomial (Fin g) K) B] (m : Ideal B) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = g := by sorry
