-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_AmbientEnumeration_ambient_refined_truncated_moment
-- name    : OAI.SharpRamseyFive.AmbientEnumeration.ambient_refined_truncated_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:52:35.328297+00:00
-- url     : https://prove2.me/theorems/c31de5a3-341b-41ec-a1e1-f5eb75f320a6
-- title:
--   OAI.SharpRamseyFive.AmbientEnumeration.ambient_refined_truncated_moment: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.AmbientEnumeration.ambient_refined_truncated_moment` of [lean/OAI/Combinatorics/SharpRamsey/Entropy/LargeCard.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/Entropy/LargeCard.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.AmbientEnumeration`, with `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators NNReal`, `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators ENNReal NNReal`, `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators NNReal`, `open Classical`, `open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents`, `open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition`, `open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination`, `open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge`, `open SharpRamseyFive.WeightedPrograms`):
--
--   ```lean
--   theorem ambient_refined_truncated_moment (weight : D → ℝ≥0) (lines : H → Finset D)
--       {p : ℕ} (hp : 0 < p) (R : ℕ) (own : H → Fin R → Bool)
--       (L : ℝ≥0) (denom rootB mass C D₀ base B : ℝ)
--       (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
--       (hlower : ∀ k, (3 / 4 : ℝ) ≤ PoissonScore.mass weight (lines k))
--       (hdelta : ∀ k, |PoissonScore.mass weight (lines k) - base| ≤ (17 / 100 : ℝ))
--       (hd : 0 < denom) (hb : 1 ≤ rootB) (hm : 0 ≤ mass) (hC : 0 ≤ C)
--       (hD : 0 ≤ D₀) (hB : 0 ≤ B)
--       (hmass : ∀ u, ∑ d ∈ lines u, ((L * weight d : ℝ≥0) : ℝ) ≤ mass)
--       (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hKR : K ≤ R / 2) (hh : 0 < h) (low : Bool)
--       (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
--       (herr : (p : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
--       (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
--       (hN₂ : ∀ d e, d ≠ e →
--         (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
--       (hBC : denom * (1 + branchingBound (V := Fin p) (B := Fin R)
--         (fun z : H × Fin p => lines z.1) (fun d => L * weight d) denom rootB mass K
--         (N₁ * p) (N₂ * p) low) ≤ C)
--       (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
--       (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
--       (hDsum : (∑ x : H, independentWeight weight (fun d => L * weight d) lines R J base x) ≤ D₀)
--       (hcost : D₀ + 2 * ((p + 1 : ℝ) * C) ≤ B * Real.exp (((L : ℝ) * R) / 5))
--       (hp2 : (p : ℝ) ^ 2 ≤ Real.exp (((L : ℝ) * R) / 10))
--       (Δ : ℕ) (hΔ : ∀ k, Fintype.card {k' : H // overlapRelation weight lines (1 / (100 * p)) k k'} ≤ Δ)
--       (hdeg : (Δ : ℝ) ≤ B * Real.exp (-((L : ℝ) * R)))
--       (hRelPairs : (Fintype.card (RelatedPair (overlapRelation weight lines (1 / (100 * p)))) : ℝ) ≤
--         B ^ 2 * Real.exp (((L : ℝ) * R) / 10)) :
--       (∫ ω, HighMoment.allTrunc R J ω *
--         (∑ k : H, scoreTerm (lines k) (Real.exp (-(L : ℝ) * base)) (own k)
--           (fun r d => ω (r,d))) ^ p
--         ∂batchMeasure (fun i : Fin R × D => L * weight i.2)) ≤
--           B ^ p * Real.exp (-(1 / 10 : ℝ) * (p * ((L : ℝ) * R)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.AmbientEnumeration.overlapRelation`, `OAI.SharpRamseyFive.ComponentEnumeration.RelatedPair`, `OAI.SharpRamseyFive.PoissonScore.batchMeasure`, `OAI.SharpRamseyFive.PoissonScore.mass`, `OAI.SharpRamseyFive.PoissonScore.scoreTerm` and `OAI.SharpRamseyFive.SingletonEnumeration.independentWeight` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.WeightedPrograms.branchingBound` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.HighMoment.allTrunc` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.SingletonEnumeration.shiftKernel` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proofs of `OAI.SharpRamseyFive.AmbientEnumeration.ambient_untruncated_moment` and `OAI.SharpRamseyFive.ScoreGeometry.actual_high_radial_moment` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/Entropy/LargeCard.lean (declaration OAI.SharpRamseyFive.AmbientEnumeration.ambient_refined_truncated_moment)

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.AmbientEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
open SharpRamseyFive.WeightedPrograms
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]

theorem ambient_refined_truncated_moment (weight : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (R : ℕ) (own : H → Fin R → Bool)
    (L : ℝ≥0) (denom rootB mass C D₀ base B : ℝ)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ k, (3 / 4 : ℝ) ≤ PoissonScore.mass weight (lines k))
    (hdelta : ∀ k, |PoissonScore.mass weight (lines k) - base| ≤ (17 / 100 : ℝ))
    (hd : 0 < denom) (hb : 1 ≤ rootB) (hm : 0 ≤ mass) (hC : 0 ≤ C)
    (hD : 0 ≤ D₀) (hB : 0 ≤ B)
    (hmass : ∀ u, ∑ d ∈ lines u, ((L * weight d : ℝ≥0) : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hKR : K ≤ R / 2) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (p : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := Fin p) (B := Fin R)
      (fun z : H × Fin p => lines z.1) (fun d => L * weight d) denom rootB mass K
      (N₁ * p) (N₂ * p) low) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (hDsum : (∑ x : H, independentWeight weight (fun d => L * weight d) lines R J base x) ≤ D₀)
    (hcost : D₀ + 2 * ((p + 1 : ℝ) * C) ≤ B * Real.exp (((L : ℝ) * R) / 5))
    (hp2 : (p : ℝ) ^ 2 ≤ Real.exp (((L : ℝ) * R) / 10))
    (Δ : ℕ) (hΔ : ∀ k, Fintype.card {k' : H // overlapRelation weight lines (1 / (100 * p)) k k'} ≤ Δ)
    (hdeg : (Δ : ℝ) ≤ B * Real.exp (-((L : ℝ) * R)))
    (hRelPairs : (Fintype.card (RelatedPair (overlapRelation weight lines (1 / (100 * p)))) : ℝ) ≤
      B ^ 2 * Real.exp (((L : ℝ) * R) / 10)) :
    (∫ ω, HighMoment.allTrunc R J ω *
      (∑ k : H, scoreTerm (lines k) (Real.exp (-(L : ℝ) * base)) (own k)
        (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => L * weight i.2)) ≤
        B ^ p * Real.exp (-(1 / 10 : ℝ) * (p * ((L : ℝ) * R))) := by
  sorry

end SharpRamseyFive.AmbientEnumeration

end

end OAI
end
