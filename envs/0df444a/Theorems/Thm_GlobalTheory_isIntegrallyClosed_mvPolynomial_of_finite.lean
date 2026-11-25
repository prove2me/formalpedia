-- Prove2me | Theorems.Thm_GlobalTheory_isIntegrallyClosed_mvPolynomial_of_finite
-- name    : GlobalTheory.isIntegrallyClosed_mvPolynomial_of_finite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:15.548519+00:00
-- url     : https://prove2.me/theorems/1a36892e-7407-4d8a-99ad-1cb38188c937
-- title:
--   Global Theory: is Integrally Closed mv Polynomial of finite
-- statement:
--   The Global Theory construction uses the is Integrally Closed mv Polynomial of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegrallyClosedMvPolynomialOfFinite.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegrallyClosedMvPolynomialOfFinite.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegrallyClosedMvPolynomialOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Frames
open GlobalTheory

theorem GlobalTheory.isIntegrallyClosed_mvPolynomial_of_finite (σ : Type) [Finite σ] (R : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsIntegrallyClosed (MvPolynomial σ R) := by sorry
