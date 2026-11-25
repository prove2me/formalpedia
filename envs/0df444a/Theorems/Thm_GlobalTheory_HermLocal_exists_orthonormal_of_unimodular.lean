-- Prove2me | Theorems.Thm_GlobalTheory_HermLocal_exists_orthonormal_of_unimodular
-- name    : GlobalTheory.HermLocal.exists_orthonormal_of_unimodular
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:06.765626+00:00
-- url     : https://prove2.me/theorems/194fd896-a26b-40a0-949f-e19b0d8db0d8
-- title:
--   Herm Local: exists orthonormal of unimodular
-- statement:
--   The Herm Local construction uses the exists orthonormal of unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L376-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L376-L387

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate WithZero
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermLocal

theorem GlobalTheory.HermLocal.exists_orthonormal_of_unimodular (R : Type) [CommRing R] (σ : R ≃+* R)
    (hσ : ∀ x, σ (σ x) = x) (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x)
    [HenselianLocalRing R₀] [Finite (IsLocalRing.ResidueField R₀)]
    (hθ : ∃ θ : R, IsUnit (θ - σ θ)) {n : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : ∀ a b, σ (A a b) = A b a) (hd : IsUnit A.det) :
    ∃ P : Matrix (Fin n) (Fin n) R, IsUnit P.det ∧ Pᵀ * A * P.map σ = 1 := by sorry
