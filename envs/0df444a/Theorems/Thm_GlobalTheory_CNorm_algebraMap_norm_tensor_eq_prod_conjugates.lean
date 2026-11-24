-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_algebraMap_norm_tensor_eq_prod_conjugates
-- name    : GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:00.420833+00:00
-- url     : https://prove2.me/theorems/3cc3b6a9-5cb6-4a7c-86d7-afb6419e824d
-- title:
--   CNorm: algebra Map norm tensor eq prod conjugates
-- statement:
--   The CNorm construction uses the algebra Map norm tensor eq prod conjugates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AlgebraMapNormTensorEqProdConjugates.lean#L11-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AlgebraMapNormTensorEqProdConjugates.lean#L11-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AlgebraMapNormTensorEqProdConjugates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped WithZero TensorProduct

theorem GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates (F E K : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [CommRing K] [Algebra F K] (y : K ⊗[F] E) :
    algebraMap K (K ⊗[F] E) (Algebra.norm K y) =
      ∏ g : E ≃ₐ[F] E, Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y := by sorry
