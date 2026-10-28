-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_centered_adjointComp_bounds_readable
-- name    : FunctionalInequalities.KLS.LogConcave.centered_adjointComp_bounds_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:13.890913+00:00
-- url     : https://prove2.me/theorems/ec846df1-cd32-4ff0-8f0d-472ede37aec2
-- title:
--   Centered Generator-Domain Bounds
-- statement:
--   This formalizes the operator-domain part of Lemma 2.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 7, for bounds (20) and (24).
--
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $m$ be an additive Haar measure on $V$, and let $\nu$ be a log-concave probability measure with nonempty interior support. Suppose that $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ for some $U:V\to\mathbb R$ of class $C^2$. Let $C\in[0,\infty)$ satisfy $C_P(\nu)\le C$, where the inequality is in $[0,\infty]$. If $u$ belongs to the domain of the adjoint composition of the closed weighted operator, and $u$ is centered, then:
--
--   $$\|u\|\le C\,\|\bar T^\dagger\bar T u\|,$$
--
--   $$\|\bar T u\|^2=\langle \bar T^\dagger\bar T u,u\rangle\le C\,\|\bar T^\dagger\bar T u\|^2,$$
--
--   and
--
--   $$\|\bar T u\|\le \sqrt C\,\|\bar T^\dagger\bar T u\|.$$
--
--   Here the norms and inner product are those of the relevant $L^2(\nu)$ spaces, and the first displayed domain element is interpreted through its underlying $L^2$ class.
--
--   This is a technical inverse-operator estimate used to control centered Poisson iterates and their gradient fields.
--
--   **Formalization Note:** The Poincaré constant is an `ENNReal` value, while $C$ is an `NNReal` whose coercions appear in the inequalities; the operator is `closedWeightedOperator` and its adjoint composition is `adjointComp`. The statement is restricted to finite-dimensional $V$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem centered_adjointComp_bounds {C : NNReal}
--       (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
--       (u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
--       (hu : L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0) :
--       ‖(u : Lp ℝ 2 (ν : Measure V))‖ ≤
--           (C : ℝ) * ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ∧
--         ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ^ 2 =
--           ⟪adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u,
--             (u : Lp ℝ 2 (ν : Measure V))⟫ ∧
--         ⟪adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u,
--             (u : Lp ℝ 2 (ν : Measure V))⟫ ≤
--           (C : ℝ) * ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^ 2 ∧
--         ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ≤
--           Real.sqrt C * ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Inverse`](https://prove2.me/theorems/fb0b02c9-17f0-4cad-9390-4ccd11bc29f3).
--
--   Definition modules: [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Supporting theorems: [`norm_le_of_gap`](https://prove2.me/theorems/bba069aa-666a-44e8-ad58-668fa76e9abb), [`closedWeightedOperator_id_gap_of_literature_le`](https://prove2.me/theorems/09f3e596-c3fd-4ea9-94f3-e85e0a602693), [`orthogonal_ker_iff_mean_eq_zero`](https://prove2.me/theorems/10368e04-91d8-41a4-9291-f17015f3bc65).
--
--   Previous: [`existsUnique_centered_adjointComp_eq`](https://prove2.me/theorems/52c0f77f-6c99-4a60-9925-c7dad4c02360).
--
--   [Source excerpt, lines 166–179](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Inverse.lean#L166-L179) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 2.1, p. 7. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Inverse.lean#L162-L285 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Inverse`, declaration `FunctionalInequalities.KLS.LogConcave.centered_adjointComp_bounds`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Inverse

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU

theorem FunctionalInequalities.KLS.LogConcave.centered_adjointComp_bounds_readable {C : NNReal}
    (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    (u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hu : L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0) :
    ‖(u : Lp ℝ 2 (ν : Measure V))‖ ≤
        (C : ℝ) * ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ∧
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ^ 2 =
        ⟪adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u,
          (u : Lp ℝ 2 (ν : Measure V))⟫ ∧
      ⟪adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u,
          (u : Lp ℝ 2 (ν : Measure V))⟫ ≤
        (C : ℝ) * ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^ 2 ∧
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ≤
        Real.sqrt C * ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ := by sorry
