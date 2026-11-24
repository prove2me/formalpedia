-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_hk_eq_sum
-- name    : GlobalTheory.CompanionTheory.HeckeMul.hk_eq_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:30.346429+00:00
-- url     : https://prove2.me/theorems/260d03d3-7bcd-48ae-ac12-7bc6b7417d5d
-- title:
--   Hecke Mul: hk eq sum
-- statement:
--   The Hecke Mul construction uses the hk eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L91-L100

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.HeckeMul.hk_eq_sum {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
    (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (w : V) (A : Finset (GL ι F ⧸ K))
    (hA : ∀ q : GL ι F ⧸ K, e q.out ≠ 0 → q ∈ A) :
    hk ρ K e w = ∑ q ∈ A, e q.out • ρ q.out w := by sorry
