-- Prove2me | Theorems.Thm_GlobalTheory_LatticePair_hasSum_pair
-- name    : GlobalTheory.LatticePair.hasSum_pair
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:00:32.736724+00:00
-- url     : https://prove2.me/theorems/311904b1-63d7-4fbc-9494-984a652ad7d9
-- title:
--   Lattice Pair: has Sum pair
-- statement:
--   The Lattice Pair construction uses the has Sum pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeckeSeriesCellHasSum.lean#L122-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeckeSeriesCellHasSum.lean#L122-L169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.LatticePair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem GlobalTheory.LatticePair.hasSum_pair (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) (g : GL (Fin n) k)
    (hg : g ∈ cell k (Fin n) ϖ e) (X : ℂ) (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) :
    HasSum (fun h : {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.1.out)).toNat +
        (ord k (Matrix.GeneralLinearGroup.det (h.1.out⁻¹ * g))).toNat))
      (X ^ (∑ i, |e i|).toNat * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) := by sorry
