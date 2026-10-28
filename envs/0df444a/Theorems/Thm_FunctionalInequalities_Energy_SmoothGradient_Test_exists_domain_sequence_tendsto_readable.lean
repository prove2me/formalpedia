-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_Test_exists_domain_sequence_tendsto_readable
-- name    : FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:02.128817+00:00
-- url     : https://prove2.me/theorems/751a102a-9a04-4eaa-a613-041165658667
-- title:
--   Smooth Test Approximation In The Lipschitz Graph Domain
-- statement:
--   This theorem supplies a graph-norm approximating sequence for every smooth test under a local-density hypothesis.
--
--   Let $V$ be a finite-dimensional complete real inner-product normed space with its Borel measurable structure and second-countable topology. Let $\nu$ be a probability measure, let $m$ be an additive Haar measure, let $D$ be a local density for $(\nu,m)$, and let $f$ be a smooth-gradient test for $\nu$. Then there exists a sequence $(p_j)$ in the domain of the Lipschitz gradient operator such that
--
--   $$
--   \bigl(p_j,\operatorname{lipschitzOperator}(p_j)\bigr)
--   \longrightarrow
--   \bigl(f.\operatorname{toL2},
--   (\operatorname{MemLp.gradient}(f)).\operatorname{toLp}(\nabla f)\bigr)
--   $$
--
--   in the product topology as $j\to\infty$. Equivalently, the $L^2$ functions and their operator images converge simultaneously.
--
--   The declaration is `Test.exists_domain_sequence_tendsto_readable`. The sequence consists of domain elements, and the gradient representative is placed in $L^2(\nu)$ using `toLp`; the statement is a convergence assertion rather than an equality at any finite index.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.SmoothGradient`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Test.exists_domain_sequence_tendsto (f : Test ν) :
--       ∃ p : ℕ → (lipschitzOperator ν m D).domain,
--         Tendsto (fun j ↦ (((p j : (lipschitzOperator ν m D).domain) : Lp ℝ 2 (ν : Measure V)),
--           lipschitzOperator ν m D (p j))) atTop
--           (𝓝 (f.toL2, (Test.memLp_gradient ν f).toLp (gradient f.toFun)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/SmoothGradient/Core`](https://prove2.me/theorems/3df73178-e378-4d68-a6db-28967184707a).
--
--   Definition modules: [`Energy/SmoothGradient/Basic`](https://prove2.me/theorems/230d76a3-8a28-41f5-a6c8-38e17a1abcdd).
--
--   Supporting theorems: [`subset_support`](https://prove2.me/theorems/4329dc1d-2277-4ded-bce3-2accbe5d4636).
--
--   Previous: [`subset_support`](https://prove2.me/theorems/4329dc1d-2277-4ded-bce3-2accbe5d4636) · Next: [`lipschitzRelaxation_le_relaxation`](https://prove2.me/theorems/92fd2438-7dfd-4386-85e1-7181a8356f84).
--
--   [Source excerpt, lines 181–185](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Core.lean#L181-L185) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Core.lean#L179-L222 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Core`, declaration `FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Core

open MeasureTheory Filter Topology
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (D : FunctionalInequalities.Energy.SmoothGradient.LocalDensity ν m)

theorem FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto_readable (f : Test ν) :
    ∃ p : ℕ → (lipschitzOperator ν m D).domain,
      Tendsto (fun j ↦ (((p j : (lipschitzOperator ν m D).domain) : Lp ℝ 2 (ν : Measure V)),
        lipschitzOperator ν m D (p j))) atTop
        (𝓝 (f.toL2, (Test.memLp_gradient ν f).toLp (gradient f.toFun))) := by sorry
