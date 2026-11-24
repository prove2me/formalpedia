-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Sphere_sum_ite_card
-- name    : GlobalTheory.CompanionTheory.UnrDens.Sphere.sum_ite_card
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:20.041873+00:00
-- url     : https://prove2.me/theorems/9b8ad0fb-0312-46d6-b10b-8d3bba6c8909
-- title:
--   Sphere: sum ite card
-- statement:
--   The Sphere construction uses the sum ite card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianVectorValuesCard.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianVectorValuesCard.lean#L30-L39

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSpaceAnisotropicUnitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianVectorValuesCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.Sphere

theorem GlobalTheory.CompanionTheory.UnrDens.Sphere.sum_ite_card {E : Type} [Fintype E] (p : E → Prop) (A B₀ : ℝ) [DecidablePred p] :
    ∑ a, (if p a then B₀ else A) =
      (Nat.card {a // p a} : ℝ) * B₀ + ((Nat.card E : ℝ) - Nat.card {a // p a}) * A := by sorry
