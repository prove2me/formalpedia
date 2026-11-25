-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_span_le_of_level
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.span_le_of_level
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:40:30.323487+00:00
-- url     : https://prove2.me/theorems/3aef963c-6df7-49d2-9887-8d3e17c34350
-- title:
--   Full Rank: span le of level
-- statement:
--   The Full Rank construction uses the span le of level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L294-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L294-L309

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.span_le_of_level (ρ : Representation ℂ H (SB X))
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x)) {K N N' : Subgroup H}
    (hK : IsCompact (K : Set H)) (hN : IsLevel K N) (hN' : IsLevel K N') (hle : N' ≤ N) (x₀ : X) {v v' : SB X}
    (hv : ∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x)
    (hv' : ∀ x, v'.1 x = (orb N' x₀).indicator (fun _ => (1 : ℂ)) x) :
    Submodule.span ℂ (Set.range fun g : H => ρ g v) ≤ Submodule.span ℂ (Set.range fun g : H => ρ g v') := by sorry
