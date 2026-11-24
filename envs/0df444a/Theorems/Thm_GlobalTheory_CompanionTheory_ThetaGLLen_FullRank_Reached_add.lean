-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_Reached_add
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.Reached.add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:43.690073+00:00
-- url     : https://prove2.me/theorems/f7ee58b3-5fd7-4192-88e5-58467923b0ca
-- title:
--   Reached: add
-- statement:
--   The Reached construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L313-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L313-L323

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
variable [T2Space X] [ContinuousSMul H X]

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.Reached.add {ρ : Representation ℂ H (SB X)}
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x))
    (hopen : ∀ x : X, IsOpenMap fun g : H => g • x) {K : Subgroup H} (hK : IsCompact (K : Set H)) {x₀ : X}
    {f f' : SB X} (h : Reached ρ K x₀ f) (h' : Reached ρ K x₀ f') :
    ∃ N : Subgroup H, IsLevel K N ∧ ∃ v : SB X, (∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x) ∧
      f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) ∧ f' ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) := by sorry
