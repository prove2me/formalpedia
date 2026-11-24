-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_act_translate
-- name    : GlobalTheory.CompanionTheory.HeckeInj.act_translate
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:31.383308+00:00
-- url     : https://prove2.me/theorems/caa3248f-75d2-4111-a2a8-a31c213a6e2b
-- title:
--   Hecke Inj: act translate
-- statement:
--   The Hecke Inj construction uses the act translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L39-L45

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
variable {G : Type} [Group G]

theorem GlobalTheory.CompanionTheory.HeckeInj.act_translate {V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G V) (A : M →ₗ[ℂ] V) (h : G) (x : G →₀ M) :
    act ρ A (Finsupp.lmapDomain M ℂ (fun g => h * g) x) = ρ h (act ρ A x) := by sorry
