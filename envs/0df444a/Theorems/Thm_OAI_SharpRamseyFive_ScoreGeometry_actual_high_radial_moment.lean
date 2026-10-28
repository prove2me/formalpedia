-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_actual_high_radial_moment
-- name    : OAI.SharpRamseyFive.ScoreGeometry.actual_high_radial_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:05:37.889402+00:00
-- url     : https://prove2.me/theorems/6b817fd6-29e0-4d98-9dab-3086a74a5f76
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.actual_high_radial_moment: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.actual_high_radial_moment` of [lean/OAI/Combinatorics/RamseyFive/Entropy/High.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Entropy/High.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory`, `open ProjectiveTraining GlobalRadial WeightedPrograms`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal`):
--
--   ```lean
--   theorem actual_high_radial_moment {J : Type} [Fintype J]
--       (hdim : finrank K V=5) (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
--       (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
--       (F : Finset (ℙ K (Dual K V)))
--       (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
--       (hf : ownFraction S (C a) (C b)≤2/25)
--       (hn : (Nat.card K:ℝ)/S.card≤1/100)
--       (L : ℝ≥0) (hL : 10000≤(L:ℝ)) (R p h : ℕ) (hp : 0<p)
--       (hKR : 200≤R/2) (hh : 0<h) (hsize : h≤(R/2-5000)/(2*200))
--       (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
--       (hx : x∉irregular (d:=4) S C ((L:ℝ)/100)) (cut : ℝ) (hcut : 1 ≤ cut)
--       (hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3)
--       (hchi : (208*2^198:ℝ)≤Real.exp (2*(((L:ℝ)*R)/100)))
--       (hmax : (pointStrength S:ℝ)*((Nat.card K:ℝ)+1)≤2)
--       (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
--       (Q : Finset (ℙ K V)) (hxQ : x∈Q)
--       (hgood : ∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
--         x∉badCenters S (fun _ => C a∪C b) (pointStrength S)
--           (((pointStrength S:ℝ)*2^i)/2) Lines Q
--           ((Nat.card K:ℝ)^4/S.card^2*Real.exp (((L:ℝ)*R)/100)/
--             (((pointStrength S:ℝ)*2^i)/2)^100))
--       (hPow : (∑z : DistinctPairs F,strength (pencilLines x F)
--         (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z^200)≤
--         dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
--           (geometryScale (Nat.card K) S.card)^2)
--       (hlocal : (pencilAlphabet (Nat.card K) 3:ℝ)*((R:ℝ)*(L:ℝ))^5000*
--           (((pointStrength S:ℝ)*((Nat.card K:ℝ)+1))^4900*
--             (2^200*((Nat.clog 2 (outsideAt x S (C a∪C b)).card:ℝ)+1)*
--               ((Nat.card K:ℝ)^4/S.card^2*Real.exp (((L:ℝ)*R)/100))))≤
--         geometryScale (Nat.card K) S.card)
--       (hcost : (40*geometryScale (Nat.card K) S.card*Real.exp ((L:ℝ)/100)+
--         geometryScale (Nat.card K) S.card)+2*((p+1:ℝ)*
--           pencilHighBudget (Nat.card K) (outsideAt x S (C a∪C b)).card S.card
--             (((L:ℝ)*R)/100) cut L p R)≤
--         geometryScale (Nat.card K) S.card*Real.exp (((L:ℝ)*R)/5))
--       (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
--       (hA : 2≤geometryScale (Nat.card K) S.card*Real.exp (-((L:ℝ)*R)))
--       (hscale : 16*((Nat.card K:ℝ)+1)≤
--         (geometryScale (Nat.card K) S.card*Real.exp (-((L:ℝ)*R)))*(1/(100*(p:ℝ)))^2)
--       (hstrong : x∉badCenters S (fun _ => C a∪C b) (pointStrength S)
--         ((1/(100*(p:ℝ)))/2) Lines Q 1)
--       (hpairScalar : (pencilAlphabet (Nat.card K) 4:ℝ)+
--         (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
--           (geometryScale (Nat.card K) S.card)^2)/(1/(100*(p:ℝ)))^200≤
--         (geometryScale (Nat.card K) S.card)^2*Real.exp (((L:ℝ)*R)/10))
--       (own : F→Fin R→Bool) :
--       (∫ω,HighMoment.allTrunc R 5000 ω*(∑H:F,scoreTerm (pencilLines x F H)
--         (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) (own H)
--         (fun r e => ω (r,e)))^p
--         ∂batchMeasure (fun i : Fin R×RadialLine x => L*
--           radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2))≤
--         (geometryScale (Nat.card K) S.card)^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.PoissonScore.batchMeasure`, `OAI.SharpRamseyFive.PoissonScore.scoreTerm`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident` and `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.GlobalRadial.badCenters`, `OAI.SharpRamseyFive.ScoreGeometry.boundedOverlapDyads`, `OAI.SharpRamseyFive.ScoreGeometry.dyadFactor`, `OAI.SharpRamseyFive.ScoreGeometry.geometryScale`, `OAI.SharpRamseyFive.ScoreGeometry.outsideAt`, `OAI.SharpRamseyFive.ScoreGeometry.pencilAlphabet`, `OAI.SharpRamseyFive.ScoreGeometry.pencilHighBudget`, `OAI.SharpRamseyFive.ScoreGeometry.pointStrength`, `OAI.SharpRamseyFive.ScoreRegularity.ownFraction`, `OAI.SharpRamseyFive.WeightedPrograms.DistinctPairs`, `OAI.SharpRamseyFive.WeightedPrograms.flat_HighMomentRecovered_7` and `OAI.SharpRamseyFive.WeightedPrograms.strength` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.HighMoment.allTrunc` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.ScoreGeometry.pencilLines`, `OAI.SharpRamseyFive.ScoreGeometry.radialWeight` and `OAI.SharpRamseyFive.ScoreRegularity.exceptional` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.ScoreRegularity.irregular` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ScoreGeometry.eventually_high_original_tail_retained` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Entropy/High.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.actual_high_radial_moment)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open ProjectiveTraining GlobalRadial WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem actual_high_radial_moment {J : Type} [Fintype J]
    (hdim : finrank K V=5) (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card≤1/100)
    (L : ℝ≥0) (hL : 10000≤(L:ℝ)) (R p h : ℕ) (hp : 0<p)
    (hKR : 200≤R/2) (hh : 0<h) (hsize : h≤(R/2-5000)/(2*200))
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (hx : x∉irregular (d:=4) S C ((L:ℝ)/100)) (cut : ℝ) (hcut : 1 ≤ cut)
    (hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hchi : (208*2^198:ℝ)≤Real.exp (2*(((L:ℝ)*R)/100)))
    (hmax : (pointStrength S:ℝ)*((Nat.card K:ℝ)+1)≤2)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hxQ : x∈Q)
    (hgood : ∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
      x∉badCenters S (fun _ => C a∪C b) (pointStrength S)
        (((pointStrength S:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/S.card^2*Real.exp (((L:ℝ)*R)/100)/
          (((pointStrength S:ℝ)*2^i)/2)^100))
    (hPow : (∑z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z^200)≤
      dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (geometryScale (Nat.card K) S.card)^2)
    (hlocal : (pencilAlphabet (Nat.card K) 3:ℝ)*((R:ℝ)*(L:ℝ))^5000*
        (((pointStrength S:ℝ)*((Nat.card K:ℝ)+1))^4900*
          (2^200*((Nat.clog 2 (outsideAt x S (C a∪C b)).card:ℝ)+1)*
            ((Nat.card K:ℝ)^4/S.card^2*Real.exp (((L:ℝ)*R)/100))))≤
      geometryScale (Nat.card K) S.card)
    (hcost : (40*geometryScale (Nat.card K) S.card*Real.exp ((L:ℝ)/100)+
      geometryScale (Nat.card K) S.card)+2*((p+1:ℝ)*
        pencilHighBudget (Nat.card K) (outsideAt x S (C a∪C b)).card S.card
          (((L:ℝ)*R)/100) cut L p R)≤
      geometryScale (Nat.card K) S.card*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hA : 2≤geometryScale (Nat.card K) S.card*Real.exp (-((L:ℝ)*R)))
    (hscale : 16*((Nat.card K:ℝ)+1)≤
      (geometryScale (Nat.card K) S.card*Real.exp (-((L:ℝ)*R)))*(1/(100*(p:ℝ)))^2)
    (hstrong : x∉badCenters S (fun _ => C a∪C b) (pointStrength S)
      ((1/(100*(p:ℝ)))/2) Lines Q 1)
    (hpairScalar : (pencilAlphabet (Nat.card K) 4:ℝ)+
      (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (geometryScale (Nat.card K) S.card)^2)/(1/(100*(p:ℝ)))^200≤
      (geometryScale (Nat.card K) S.card)^2*Real.exp (((L:ℝ)*R)/10))
    (own : F→Fin R→Bool) :
    (∫ω,HighMoment.allTrunc R 5000 ω*(∑H:F,scoreTerm (pencilLines x F H)
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) (own H)
      (fun r e => ω (r,e)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*
        radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2))≤
      (geometryScale (Nat.card K) S.card)^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  sorry

end SharpRamseyFive.ScoreGeometry

end OAI
end
