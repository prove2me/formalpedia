-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_compLp_innerSL_closedWeightedOperator_comm_readable
-- name    : FunctionalInequalities.KLS.LogConcave.compLp_innerSL_closedWeightedOperator_comm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:38.691018+00:00
-- url     : https://prove2.me/theorems/9523c342-5f06-4597-bd28-317e4e2a8f9d
-- title:
--   Symmetry of the Weak Hessian
-- statement:
--   This formalizes the symmetry part of the weak Hessian estimate associated with BKL Equation (16), p. 6.
--
--   Let $V$ be finite-dimensional, let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$, where $U$ has temperate growth, and assume all exponential moments of $\nu$ are integrable. Let $F\in D(A)$, with $A=\bar T^\dagger\bar T$. Suppose that for every coordinate index $i$, the weak first derivative
--
--   $$\partial_iF=\langle e_i,\bar TF\rangle$$
--
--   belongs to the domain of $\bar T$. Then for all coordinate indices $i,j$,
--
--   $$\langle e_j,\bar T\partial_iF\rangle
--   =\langle e_i,\bar T\partial_jF\rangle$$
--
--   as elements of $L^2(\nu)$. Here $e_i,e_j$ are the standard orthonormal basis vectors.
--
--   This is the operator-domain symmetry of the weak Hessian used in curvature and defect arguments.
--
--   **Formalization Note:** The equality is equality of `compLp` $L^2(\nu)$ classes; it does not assert classical pointwise second derivatives of $F$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem compLp_innerSL_closedWeightedOperator_comm
--       (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
--       (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
--       (hD : ∀ i, (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
--           (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
--             ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
--         (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
--       (i j : Fin (Module.finrank ℝ V)) :
--       (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp
--           (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD i⟩) =
--         (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
--           (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD j⟩)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Hessian`](https://prove2.me/theorems/9ec9f121-cade-4400-bbdd-811b2f170da2).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`convexOn_of_eq_tilted`](https://prove2.me/theorems/c25e8adc-034c-4eda-8eb4-4a844cb9f0fc), [`exists_seq_smooth_tendsto_weakHessian`](https://prove2.me/theorems/710e036c-fb9b-40b7-ba2f-f65dc86dd10f).
--
--   Previous: [`exists_seq_smooth_tendsto_weakHessian`](https://prove2.me/theorems/710e036c-fb9b-40b7-ba2f-f65dc86dd10f).
--
--   [Source excerpt, lines 365–377](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Hessian.lean#L365-L377) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (16), p. 6 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Hessian.lean#L363-L396 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Hessian`, declaration `FunctionalInequalities.KLS.LogConcave.compLp_innerSL_closedWeightedOperator_comm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.compLp_innerSL_closedWeightedOperator_comm_readable
    (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hD : ∀ i, (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (i j : Fin (Module.finrank ℝ V)) :
    (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD i⟩) =
      (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD j⟩) := by sorry
