-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_unr_embedding
-- name    : GlobalTheory.UnitLemma.Unr.exists_unr_embedding
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:37:42.476057+00:00
-- url     : https://prove2.me/theorems/eecf7ec5-fbbe-442c-b6d7-67a0d10a78a3
-- title:
--   Unr: exists unr embedding
-- statement:
--   The Unr construction uses the exists unr embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedInvolutionFieldEmbedding.lean#L52-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedInvolutionFieldEmbedding.lean#L52-L219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MonicDvdXPowCardSubOneExistsRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionResiduePowAndRootsOfUnityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinPrimitiveRootEqIntegersUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedInvolutionFieldEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial IsLocalRing

theorem GlobalTheory.UnitLemma.Unr.exists_unr_embedding : ∀ (K : UQ), K.Odd → ∀ B : InvAlg K, B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) (d : ℕ), Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) → ∀ (K' : UQ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → (∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤) → ∃ (ψ : K'.E →+* B.A) (_ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (_ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)), ∃ s : K'.Oˣ, algebraMap K'.O K'.E s * K'.c (algebraMap K'.O K'.E s) = 1 ∧ @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ := by sorry
