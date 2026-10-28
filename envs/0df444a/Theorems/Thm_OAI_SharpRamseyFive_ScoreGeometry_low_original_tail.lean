-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_low_original_tail
-- name    : OAI.SharpRamseyFive.ScoreGeometry.low_original_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:08:29.741693+00:00
-- url     : https://prove2.me/theorems/a1a95d55-e11d-441d-94a2-16b504405e2c
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.low_original_tail: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.low_original_tail` of [lean/OAI/Combinatorics/RamseyFive/Probability/UniformTails.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Probability/UniformTails.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal`):
--
--   ```lean
--   theorem low_original_tail {d : ℕ} (hdim : finrank K V=d+1) (hd : 2≤d)
--       {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
--       (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
--       (F : Finset (ℙ K (Dual K V)))
--       (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
--       (hf : ownFraction S (C a) (C b)≤2/25)
--       (hn : (Nat.card K:ℝ)/S.card≤1/100)
--       (L : ℝ≥0) (hL : 10000≤(L:ℝ)) (R p h : ℕ) (hp : 0<p) (heven : Even p) (hKR : 200≤R/2)
--       (hh : 0<h) (hsize : h≤(R/2)/(2*200))
--       (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
--       (hx : x∉irregular (d:=d) S C ((L:ℝ)/100)) (cut : ℝ) (hcut : 1 ≤ cut)
--       (hpairs : ∀u:ℝ,0<u → u≤2 →
--         ((Finset.univ.filter fun z:WeightedPrograms.DistinctPairs F =>
--           u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
--             (pencilLines x F z.1∩pencilLines x F z.2.val)).card:ℝ)*u^200≤
--           (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/50))
--       (hrows : ∀H:F,∀u:ℝ,0<u → u≤2 →
--         ((Finset.univ.filter fun H':F => H≠H' ∧ u ≤ mass
--           (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
--           (pencilLines x F H∩pencilLines x F H')).card:ℝ)*u^200≤
--           scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/50))
--       (hdegree : ∀H:F,
--         ((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(p:ℝ)) ≤ mass
--           (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
--           (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤
--           scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R)))
--       (hdegreeScalar : 2+scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R))≤
--           scale (K:=K) d S.card*Real.exp (-((L:ℝ)*R)))
--       (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
--       (hpairScalar : (pencilAlphabet (Nat.card K) d:ℝ)+
--         (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
--           (scale (K:=K) d S.card)^2)/(1/(100*(p:ℝ)))^200≤
--         (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/10))
--       (hcost : 40*scale (K:=K) d S.card*Real.exp ((L:ℝ)/100)+
--         2*((p+1:ℝ)*lowMomentBudget (pencilAlphabet (Nat.card K) d)
--           (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*(scale (K:=K) d S.card)^2)
--           (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*scale (K:=K) d S.card)
--           (scale (K:=K) d S.card) cut L p R
--           (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2)))≤
--         scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/5))
--       {κ t : ℝ} (hκ : κ+Real.log 10≤((L:ℝ)*R)/20)
--       (hpP : 1000*Real.log (Nat.card K)≤(p:ℝ)*((L:ℝ)*R))
--       (ht : scale (K:=K) d S.card*Real.exp (-κ)/10≤t) :
--       (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
--         {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
--           (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
--         (Nat.card K:ℝ)^(-(50:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.PoissonScore.mass`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident` and `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ScoreGeometry.Unsampled`, `OAI.SharpRamseyFive.ScoreGeometry.dyadFactor`, `OAI.SharpRamseyFive.ScoreGeometry.lowMomentBudget`, `OAI.SharpRamseyFive.ScoreGeometry.outsideAt`, `OAI.SharpRamseyFive.ScoreGeometry.pencilAlphabet`, `OAI.SharpRamseyFive.ScoreGeometry.pointStrength`, `OAI.SharpRamseyFive.ScoreRegularity.ownFraction`, `OAI.SharpRamseyFive.ScoreRegularity.scale`, `OAI.SharpRamseyFive.WeightedPrograms.DistinctPairs` and `OAI.SharpRamseyFive.WeightedPrograms.flat_HighMomentRecovered_7` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.PoissonScore.scheduleMeasure`, `OAI.SharpRamseyFive.ScoreGeometry.pencilLines`, `OAI.SharpRamseyFive.ScoreGeometry.pointScore`, `OAI.SharpRamseyFive.ScoreGeometry.radialWeight` and `OAI.SharpRamseyFive.ScoreRegularity.exceptional` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.ScoreRegularity.irregular` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proofs of `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_ambient_tail`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_low_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_ambient_tail_cases` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Probability/UniformTails.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.low_original_tail)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem low_original_tail {d : ℕ} (hdim : finrank K V=d+1) (hd : 2≤d)
    {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card≤1/100)
    (L : ℝ≥0) (hL : 10000≤(L:ℝ)) (R p h : ℕ) (hp : 0<p) (heven : Even p) (hKR : 200≤R/2)
    (hh : 0<h) (hsize : h≤(R/2)/(2*200))
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (hx : x∉irregular (d:=d) S C ((L:ℝ)/100)) (cut : ℝ) (hcut : 1 ≤ cut)
    (hpairs : ∀u:ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun z:WeightedPrograms.DistinctPairs F =>
        u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F z.1∩pencilLines x F z.2.val)).card:ℝ)*u^200≤
        (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/50))
    (hrows : ∀H:F,∀u:ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun H':F => H≠H' ∧ u ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)*u^200≤
        scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/50))
    (hdegree : ∀H:F,
      ((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(p:ℝ)) ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤
        scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R)))
    (hdegreeScalar : 2+scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R))≤
        scale (K:=K) d S.card*Real.exp (-((L:ℝ)*R)))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hpairScalar : (pencilAlphabet (Nat.card K) d:ℝ)+
      (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (scale (K:=K) d S.card)^2)/(1/(100*(p:ℝ)))^200≤
      (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/10))
    (hcost : 40*scale (K:=K) d S.card*Real.exp ((L:ℝ)/100)+
      2*((p+1:ℝ)*lowMomentBudget (pencilAlphabet (Nat.card K) d)
        (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*(scale (K:=K) d S.card)^2)
        (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*scale (K:=K) d S.card)
        (scale (K:=K) d S.card) cut L p R
        (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2)))≤
      scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/5))
    {κ t : ℝ} (hκ : κ+Real.log 10≤((L:ℝ)*R)/20)
    (hpP : 1000*Real.log (Nat.card K)≤(p:ℝ)*((L:ℝ)*R))
    (ht : scale (K:=K) d S.card*Real.exp (-κ)/10≤t) :
    (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
      {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
        (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
      (Nat.card K:ℝ)^(-(50:ℝ)) := by
  sorry

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end
