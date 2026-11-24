-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_translate_mem_span
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.translate_mem_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:40:11.002803+00:00
-- url     : https://prove2.me/theorems/ad9895f6-f0ad-4920-9ebf-e9766b951acd
-- title:
--   Full Rank: translate mem span
-- statement:
--   The Full Rank construction uses the translate mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L170-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L170-L178

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
variable {H X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace X] [MulAction H X]

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.translate_mem_span {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (t : V) (g : H)
    {w : V} (hw : w ∈ Submodule.span ℂ (Set.range fun h : H => ρ h t)) :
    ρ g w ∈ Submodule.span ℂ (Set.range fun h : H => ρ h t) := by sorry
