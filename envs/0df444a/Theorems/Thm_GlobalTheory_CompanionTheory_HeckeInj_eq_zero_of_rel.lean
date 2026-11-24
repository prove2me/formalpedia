-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_eq_zero_of_rel
-- name    : GlobalTheory.CompanionTheory.HeckeInj.eq_zero_of_rel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:20.264794+00:00
-- url     : https://prove2.me/theorems/049a7dd1-762f-4e4b-9fca-9bd53138e9bf
-- title:
--   Hecke Inj: eq zero of rel
-- statement:
--   The Hecke Inj construction uses the eq zero of rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L172-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L172-L193

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.HeckeInj.eq_zero_of_rel {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F)))
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL ι F) V) (τ : Representation ℂ (GL ι F) W) (T : V →ₗ[ℂ] W)
    (hfix : ∀ v ∈ fixed π K, T v ∈ fixed τ K)
    (hT : ∀ e, IsHk K e → ∀ v ∈ fixed π K, T (hk π K e v) = hk τ K e (T v))
    (x : GL ι F →₀ fixed π K) (ha : act π (fixed π K).subtype x = 0)
    (hb : act τ (T ∘ₗ (fixed π K).subtype) x ∈ fixed τ K) :
    act τ (T ∘ₗ (fixed π K).subtype) x = 0 := by sorry
