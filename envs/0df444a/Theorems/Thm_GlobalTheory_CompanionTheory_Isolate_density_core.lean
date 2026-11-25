-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Isolate_density_core
-- name    : GlobalTheory.CompanionTheory.Isolate.density_core
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:07.399592+00:00
-- url     : https://prove2.me/theorems/ff69c066-b1ef-494c-97ed-ff5e91a0f089
-- title:
--   Isolate: density core
-- statement:
--   The Isolate construction uses the density core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsolateRepresentationAtCharacter.lean#L373-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsolateRepresentationAtCharacter.lean#L373-L435

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

theorem GlobalTheory.CompanionTheory.Isolate.density_core {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F)))
    (hKc : IsCompact (K : Set (GL ι F))) {I : Type} [Fintype I] {Y : I → Type}
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (ρ : ∀ i, Representation ℂ (GL ι F) (Y i))
    (hs : ∀ i, IsSmooth (ρ i)) (hi : ∀ i, (ρ i).IsIrreducible)
    (h0 : ∀ i, ∃ v ∈ fixed (ρ i) K, v ≠ 0)
    (hne : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j)
    (f : ∀ i, Module.End ℂ (fixed (ρ i) K)) :
    ∃ e, IsHk K e ∧ ∀ i (x : fixed (ρ i) K), hk (ρ i) K e x = (f i x : Y i) := by sorry
