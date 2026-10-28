-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_cell_score_from_integrals
-- name    : OAI.SharpRamseyFive.ScoreGeometry.cell_score_from_integrals
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:05:04.268719+00:00
-- url     : https://prove2.me/theorems/4d9faca5-316a-4179-b87b-98f9099c5ca0
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.cell_score_from_integrals: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.cell_score_from_integrals` of [lean/OAI/Combinatorics/RamseyFive/Iteration/CellScoreProcedure.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Iteration/CellScoreProcedure.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence CellVariance ScoreRegularity`, `open MeasureTheory ProbabilityTheory PoissonScore`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal`):
--
--   ```lean
--   theorem cell_score_from_integrals {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
--       (hq : (10:ℝ)≤Nat.card K) (X U S : Finset (ℙ K V)) (hSX : S⊆X) (hSU : S⊆U)
--       (hS : S.Nonempty) (hret : X.card≤4*S.card)
--       {J : Type*} [Fintype J] (C : J→Finset (ℙ K V))
--       (hC : (∑j,(C j).card)≤3*S.card) (ia ib : ℙ K V→J)
--       (hf : ∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25)
--       (T : Finset (ℙ K (Dual K V))) (L : ℝ≥0) (R : ℕ) (b τ CP : ℝ)
--       (hτ : 0<τ) (hτhi : 8*τ≤4/5)
--       (hdensity : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card)
--       (hprod : (Nat.card K:ℝ)^(d+1)*Real.exp (-b)≤(X.card:ℝ)*T.card)
--       (hP : 104≤(L:ℝ)*R) (hCP : 0≤CP)
--       (hnP : (Nat.card K:ℝ)*((L:ℝ)*R)≤S.card)
--       (hbad : ((irregular (d:=d) S C ((L:ℝ)/100)).card:ℝ)≤(S.card:ℝ)/100)
--       (he : b+16*((L:ℝ)*R)*τ+Real.log 16+Real.log 3200000000≤((L:ℝ)*R)/2000)
--       (hs : 8*((L:ℝ)*R)*τ+Real.log 1600≤(L:ℝ)/1000)
--       (hu : 8*((L:ℝ)*R)*τ+Real.log 16≤(L:ℝ)*R)
--       (hk : b+8*((L:ℝ)*R)*τ+Real.log 16≤(L:ℝ)*R)
--       (hκL : b+8*((L:ℝ)*R)*τ+Real.log 16+Real.log 100≤(91/100:ℝ)*(L:ℝ))
--       (hR : (R:ℝ)*Real.exp (-(23/25:ℝ)*(L:ℝ))≤1/10)
--       (htrain : (∫ω,((typicalFailures S S (fun x => C (ia x)∪C (ib x)) (exceptional S C)
--         (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x)))))
--         (scale (K:=K) d S.card*Real.exp (-(b+8*((L:ℝ)*R)*τ+Real.log 16))/10) ω).card:ℝ)
--         ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤(S.card:ℝ)*Real.exp (-(L:ℝ)/1000))
--       (hamb : (∫ω,((typicalFailures U S (fun x => C (ia x)∪C (ib x)) (exceptional S C)
--         (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x)))))
--         (scale (K:=K) d S.card*Real.exp (-(b+8*((L:ℝ)*R)*τ+Real.log 16))/10) ω).card:ℝ)
--         ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤(S.card:ℝ)*Real.exp (CP*((L:ℝ)*R))) :
--       Real.exp (-8*((L:ℝ)*R)*τ)/4≤
--       (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
--         {ω | let W := decoded U S (fun x => C (ia x)∪C (ib x)) (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))) (emptyTests (exceptional S C) (hyperplaneSupport S) ω).card ω
--           (sampleCount ω:ℝ)≤2*((Nat.card K:ℝ)*((L:ℝ)*R)) ∧
--           (W.card:ℝ)≤(S.card:ℝ)*Real.exp ((CP+2)*((L:ℝ)*R)) ∧
--           (9/10:ℝ)*S.card≤((W∩S).card:ℝ)}
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.PoissonScore.sampleCount`, `OAI.SharpRamseyFive.ScoreGeometry.pointStrength`, `OAI.SharpRamseyFive.ScoreRegularity.ownFraction` and `OAI.SharpRamseyFive.ScoreRegularity.scale` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.incidences` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.PoissonScore.emptyTests`, `OAI.SharpRamseyFive.PoissonScore.scheduleMeasure`, `OAI.SharpRamseyFive.ScoreGeometry.decoded`, `OAI.SharpRamseyFive.ScoreGeometry.hyperplaneSupport`, `OAI.SharpRamseyFive.ScoreGeometry.typicalFailures` and `OAI.SharpRamseyFive.ScoreRegularity.exceptional` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.ScoreRegularity.irregular` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proofs of `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_procedure` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Iteration/CellScoreProcedure.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.cell_score_from_integrals)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem cell_score_from_integrals {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : (10:ℝ)≤Nat.card K) (X U S : Finset (ℙ K V)) (hSX : S⊆X) (hSU : S⊆U)
    (hS : S.Nonempty) (hret : X.card≤4*S.card)
    {J : Type*} [Fintype J] (C : J→Finset (ℙ K V))
    (hC : (∑j,(C j).card)≤3*S.card) (ia ib : ℙ K V→J)
    (hf : ∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25)
    (T : Finset (ℙ K (Dual K V))) (L : ℝ≥0) (R : ℕ) (b τ CP : ℝ)
    (hτ : 0<τ) (hτhi : 8*τ≤4/5)
    (hdensity : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card)
    (hprod : (Nat.card K:ℝ)^(d+1)*Real.exp (-b)≤(X.card:ℝ)*T.card)
    (hP : 104≤(L:ℝ)*R) (hCP : 0≤CP)
    (hnP : (Nat.card K:ℝ)*((L:ℝ)*R)≤S.card)
    (hbad : ((irregular (d:=d) S C ((L:ℝ)/100)).card:ℝ)≤(S.card:ℝ)/100)
    (he : b+16*((L:ℝ)*R)*τ+Real.log 16+Real.log 3200000000≤((L:ℝ)*R)/2000)
    (hs : 8*((L:ℝ)*R)*τ+Real.log 1600≤(L:ℝ)/1000)
    (hu : 8*((L:ℝ)*R)*τ+Real.log 16≤(L:ℝ)*R)
    (hk : b+8*((L:ℝ)*R)*τ+Real.log 16≤(L:ℝ)*R)
    (hκL : b+8*((L:ℝ)*R)*τ+Real.log 16+Real.log 100≤(91/100:ℝ)*(L:ℝ))
    (hR : (R:ℝ)*Real.exp (-(23/25:ℝ)*(L:ℝ))≤1/10)
    (htrain : (∫ω,((typicalFailures S S (fun x => C (ia x)∪C (ib x)) (exceptional S C)
      (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x)))))
      (scale (K:=K) d S.card*Real.exp (-(b+8*((L:ℝ)*R)*τ+Real.log 16))/10) ω).card:ℝ)
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤(S.card:ℝ)*Real.exp (-(L:ℝ)/1000))
    (hamb : (∫ω,((typicalFailures U S (fun x => C (ia x)∪C (ib x)) (exceptional S C)
      (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x)))))
      (scale (K:=K) d S.card*Real.exp (-(b+8*((L:ℝ)*R)*τ+Real.log 16))/10) ω).card:ℝ)
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤(S.card:ℝ)*Real.exp (CP*((L:ℝ)*R))) :
    Real.exp (-8*((L:ℝ)*R)*τ)/4≤
    (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
      {ω | let W := decoded U S (fun x => C (ia x)∪C (ib x)) (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))) (emptyTests (exceptional S C) (hyperplaneSupport S) ω).card ω
        (sampleCount ω:ℝ)≤2*((Nat.card K:ℝ)*((L:ℝ)*R)) ∧
        (W.card:ℝ)≤(S.card:ℝ)*Real.exp ((CP+2)*((L:ℝ)*R)) ∧
        (9/10:ℝ)*S.card≤((W∩S).card:ℝ)} := by
  sorry

end SharpRamseyFive.ScoreGeometry

end OAI
end
