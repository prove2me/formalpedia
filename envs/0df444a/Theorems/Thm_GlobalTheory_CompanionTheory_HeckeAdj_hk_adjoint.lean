-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAdj_hk_adjoint
-- name    : GlobalTheory.CompanionTheory.HeckeAdj.hk_adjoint
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:52.948974+00:00
-- url     : https://prove2.me/theorems/61525103-994e-4dd1-9f7c-bd5f14a642a5
-- title:
--   Hecke Adj: hk adjoint
-- statement:
--   The Hecke Adj construction uses the hk adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOutNeZero.lean#L143-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOutNeZero.lean#L143-L160

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOutNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeAdj

theorem GlobalTheory.CompanionTheory.HeckeAdj.hk_adjoint : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    IsHk K (hstar e) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
      (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ g v w, B (ρ g v) (ρ g w) = B v w) → ∀ v ∈ fixed ρ K, ∀ w ∈ fixed ρ K,
      B (hk ρ K e v) w = B v (hk ρ K (hstar e) w) := by sorry
