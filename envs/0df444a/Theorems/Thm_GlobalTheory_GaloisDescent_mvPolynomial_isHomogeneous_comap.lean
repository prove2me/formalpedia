-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_mvPolynomial_isHomogeneous_comap
-- name    : GlobalTheory.GaloisDescent.mvPolynomial_isHomogeneous_comap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:42.263084+00:00
-- url     : https://prove2.me/theorems/01adea3d-107d-562c-9e07-2166265fc41c
-- title:
--   Galois Descent: mv Polynomial is Homogeneous comap
-- statement:
--   The Galois Descent construction uses the mv Polynomial is Homogeneous comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L114-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
open MvPolynomial
variable {K L G σ : Type*} [Field K] [Field L] [Algebra K L]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.GaloisDescent.mvPolynomial_isHomogeneous_comap {I : Ideal (MvPolynomial σ L)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) :
    (I.comap (map (algebraMap K L) : MvPolynomial σ K →+* _)).IsHomogeneous
      (homogeneousSubmodule σ K) := by sorry
