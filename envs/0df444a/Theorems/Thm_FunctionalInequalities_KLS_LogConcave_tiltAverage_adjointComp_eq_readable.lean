-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_tiltAverage_adjointComp_eq_readable
-- name    : FunctionalInequalities.KLS.LogConcave.tiltAverage_adjointComp_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:45.537089+00:00
-- url     : https://prove2.me/theorems/7fe24b66-7194-4dbb-bf46-4b6ea812f082
-- title:
--   Tilt-Average Identity on the Generator Domain
-- statement:
--   This formalizes the tilted generator identity (48) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Equation (48), p. 14.
--
--   Let $V$ be finite-dimensional, let $\nu$ be a log-concave probability measure with nonempty interior support, and let $m$ be Haar measure. Assume $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ for a function $U\in C^1(V)$, and assume all exponential moments are integrable:
--
--   $$\forall r\in\mathbb R,\qquad \int e^{r\|x\|}\,d\nu(x)<\infty.$$
--
--   For every $F$ in the domain of $A=\bar T^\dagger\bar T$ and every $z\in V$, the tilt average of $AF$ equals the inner product of $z$ with the tilt average of $\bar TF$:
--
--   $$F_{AF}(z)=\left\langle z,F_{\bar TF}(z)\right\rangle.$$
--
--   The representatives involved are the $L^2(\nu)$ classes of $AF$ and $\bar TF$.
--
--   This identity is the domain-level form of the integration-by-parts relation used to derive Taylor-tensor recursions.
--
--   **Formalization Note:** The definition `tiltAverage` is applied to the $L^2$ representatives supplied by `adjointComp` and `closedWeightedOperator`; no pointwise regularity of $F$ is asserted.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tiltAverage_adjointComp_eq (hνU : (ν : Measure V) = m.tilted (-U))
--       (hU : ContDiff ℝ 1 U)
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
--       (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
--       (z : V) :
--       tiltAverage (ν : Measure V)
--           (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) z =
--         ⟪z, tiltAverage (ν : Measure V)
--           (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
--             ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) z⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Tilt`](https://prove2.me/theorems/c32ba817-f9ca-4787-8cee-e05ffed04129).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`integrable_expTilt_of_memLp`](https://prove2.me/theorems/92338882-be7b-4eaa-bd08-2e7a5b6bd38c), [`tiltAverage_neg_weightedLaplacian`](https://prove2.me/theorems/2049b0ee-2e67-44f2-a194-81ea5ae5e577), [`tendsto_apply_of_tendsto_adjointComp`](https://prove2.me/theorems/89a4caec-afca-4ac9-a5f0-98cc15c7d63d), [`exists_seq_smooth_tendsto_adjointComp_of_localRegularity`](https://prove2.me/theorems/7b48e926-80ae-40b4-a5a6-d33d9c1a1273), [`toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`](https://prove2.me/theorems/44e63681-21ce-4775-a563-130ebf063881).
--
--   [Source excerpt, lines 81–90](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Tilt.lean#L81-L90) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (48), p. 14 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Tilt.lean#L79-L109 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Tilt`, declaration `FunctionalInequalities.KLS.LogConcave.tiltAverage_adjointComp_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Tilt

open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace ENNReal
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.tiltAverage_adjointComp_eq_readable (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (z : V) :
    tiltAverage (ν : Measure V)
        (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) z =
      ⟪z, tiltAverage (ν : Measure V)
        (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) z⟫ := by sorry
