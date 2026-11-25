-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_independence_under_negligible_weak_limit_perturbations
-- name    : ManyServerQED.Scheduling.independence_under_negligible_weak_limit_perturbations
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T21:05:28.314938+00:00
-- url     : https://prove2.me/theorems/a9ab254c-ef8c-4a4a-832c-537fac18c478
-- title:
--   Independence in a weak joint limit with negligible perturbations
-- statement:
--   Suppose $(X_n,Y_n)$ converges jointly in distribution to $(X,Y)$, and $V_n-Y_n$ tends to zero in probability. If $X_n$ and $V_n$ are independent for all sufficiently large $n$, then $X$ and $Y$ are independent.
-- source:
--   Supporting lemma for the proof of Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology Complex

theorem ManyServerQED.Scheduling.independence_under_negligible_weak_limit_perturbations
    {Ω Ω' E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [SecondCountableTopology F]
    [MeasurableSpace F] [BorelSpace F]
    (X : ℕ → Ω → E) (Y V : ℕ → Ω → F) (x : Ω' → E) (y : Ω' → F)
    (h : TendstoInDistribution (fun n ω => (X n ω,Y n ω)) atTop
      (fun ω => (x ω,y ω)) (fun _ => P) P')
    (hV : ∀ n, AEMeasurable (V n) P)
    (herr : TendstoInMeasure P (fun n ω => V n ω - Y n ω) atTop (fun _ => 0))
    (hind : ∀ᶠ n in atTop, IndepFun (X n) (V n) P) :
    IndepFun x y P' := by sorry
