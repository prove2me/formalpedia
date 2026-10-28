-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_existsUnique_centered_adjointComp_eq_readable
-- name    : FunctionalInequalities.KLS.LogConcave.existsUnique_centered_adjointComp_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:17.789496+00:00
-- url     : https://prove2.me/theorems/52c0f77f-6c99-4a60-9925-c7dad4c02360
-- title:
--   Unique Centered Generator Preimage
-- statement:
--   This formalizes the existence-and-uniqueness part of Lemma 2.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 7.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $\nu$ be a log-concave probability measure with nonempty interior support. Assume that $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ for a $C^2$ function $U:V\to\mathbb R$. Let $C\in[0,\infty)$ satisfy $C_P(\nu)\le C$. For every centered $g\in L^2(\nu)$, there exists exactly one element $u$ in the domain of the adjoint composition of the closed weighted operator such that $u$ is centered and its adjoint composition equals $g$:
--
--   $$\exists!\,u\in D(\bar T^\dagger\bar T),\qquad \int u\,d\nu=0\quad\text{and}\quad \bar T^\dagger\bar T u=g.$$
--
--   The uniqueness is among domain elements satisfying both displayed conditions.
--
--   This provides the centered inverse of the generator for subsequent operator-domain constructions.
--
--   **Formalization Note:** `L2.mean` expresses centering, and equality of the adjoint composition is equality in the $L^2(\nu)$ space. The Poincaré comparison is between the `ENNReal` intrinsic constant and the coercion of $C\in\mathrm{NNReal}$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem existsUnique_centered_adjointComp_eq {C : NNReal}
--       (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
--       (g : Lp ℝ 2 (ν : Measure V)) (hg : L2.mean ν g = 0) :
--       ∃! u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
--         L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧
--           adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u = g
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Inverse`](https://prove2.me/theorems/fb0b02c9-17f0-4cad-9390-4ccd11bc29f3).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Supporting theorems: [`eq_of_adjointComp_eq`](https://prove2.me/theorems/6574e2a9-9b4d-48e4-99c5-802eaa15ee6d), [`exists_adjointComp_eq_of_gap`](https://prove2.me/theorems/4fa4bc87-0c47-4025-88c0-329b6fe87034), [`closedWeightedOperator_id_gap_of_literature_le`](https://prove2.me/theorems/09f3e596-c3fd-4ea9-94f3-e85e0a602693), [`orthogonal_ker_iff_mean_eq_zero`](https://prove2.me/theorems/10368e04-91d8-41a4-9291-f17015f3bc65).
--
--   Previous: [`orthogonal_ker_iff_mean_eq_zero`](https://prove2.me/theorems/10368e04-91d8-41a4-9291-f17015f3bc65) · Next: [`centered_adjointComp_bounds`](https://prove2.me/theorems/ec846df1-cd32-4ff0-8f0d-472ede37aec2).
--
--   [Source excerpt, lines 105–110](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Inverse.lean#L105-L110) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 2.1, p. 7. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Inverse.lean#L101-L160 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Inverse`, declaration `FunctionalInequalities.KLS.LogConcave.existsUnique_centered_adjointComp_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Inverse

open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU

theorem FunctionalInequalities.KLS.LogConcave.existsUnique_centered_adjointComp_eq_readable {C : NNReal}
    (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    (g : Lp ℝ 2 (ν : Measure V)) (hg : L2.mean ν g = 0) :
    ∃! u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧
        adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u = g := by sorry
