-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_mem_span_translates_of_level
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.mem_span_translates_of_level
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:53.211949+00:00
-- url     : https://prove2.me/theorems/d6502f39-2d24-4017-9bb4-c715e5886a10
-- title:
--   Full Rank: mem span translates of level
-- statement:
--   The Full Rank construction uses the mem span translates of level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L226-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L226-L292

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.mem_span_translates_of_level : ∀ (H X : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace X] [MulAction H X] (ρ : Representation ℂ H (SB X)), (∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x)) → ∀ (K N : Subgroup H), IsCompact (K : Set H) → IsOpen (N : Set H) → N ≤ K → (∀ κ ∈ K, ∀ n ∈ N, κ * n * κ⁻¹ ∈ N) → ∀ (x₀ : X) (v f : SB X), (∀ x, v.1 x = ((fun n : H => n • x₀) '' (N : Set H)).indicator (fun _ => (1 : ℂ)) x) → (∀ n ∈ N, ∀ x, f.1 (n • x) = f.1 x) → (∀ x, f.1 x ≠ 0 → x ∈ (fun κ : H => κ • x₀) '' (K : Set H)) → f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) := by sorry
