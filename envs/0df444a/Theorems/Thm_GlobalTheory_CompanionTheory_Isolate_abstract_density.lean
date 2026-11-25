-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Isolate_abstract_density
-- name    : GlobalTheory.CompanionTheory.Isolate.abstract_density
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:19.389147+00:00
-- url     : https://prove2.me/theorems/e29010ca-982c-5671-8f46-fc9203df0bac
-- title:
--   Isolate: abstract density
-- statement:
--   The Isolate construction uses the abstract density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsolateRepresentationAtCharacter.lean#L314-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsolateRepresentationAtCharacter.lean#L314-L337

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HkMemFixed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsolateRepresentationAtCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Isolate
open GlobalTheory.CompanionTheory.HeckeMul
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.Isolate.abstract_density {I : Type} [Fintype I] (M : I → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, FiniteDimensional ℂ (M i)] [∀ i, Nontrivial (M i)]
    (A : Subalgebra ℂ (∀ i, Module.End ℂ (M i)))
    (hsimple : ∀ i (S : Submodule ℂ (M i)), (∀ a ∈ A, ∀ x ∈ S, a i x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hiso : ∀ i j (φ : M i ≃ₗ[ℂ] M j), (∀ a ∈ A, ∀ x, φ (a i x) = a j (φ x)) → i = j)
    (f : ∀ i, Module.End ℂ (M i)) : ∃ a ∈ A, ∀ i, a i = f i := by sorry
