-- Prove2me | Theorems.Thm_LogMeanVar_Complete_Supplement_theorem_1
-- name    : LogMeanVar.Complete.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:00:31.313808+00:00
-- url     : https://prove2.me/theorems/afbab937-f94f-4824-abe0-3c33ad1c3bb6
-- title:
--   Theorem 1 — log-MV equilibrium implies fixed-target variance equilibrium
-- statement:
--   Let the scalar stochastic market and its actual state/log-return equations be as in (1), (5) and (6). Let $\gamma_t$ be an adapted, strictly positive preference process; it need not be constant. Suppose $\widehat\pi$ is an equilibrium for the log-return mean–variance criterion (7), with reference return $\widehat R$, and let its fixed adapted annual target be
--
--   $$\widehat a_t=\frac{\mathbb E_t[\widehat R_T]-\widehat R_t}{T-t},\qquad 0\le t<T.$$
--
--   Then $\widehat\pi$ is an equilibrium for variance minimization (8) with target $\widehat a$. Every admissible constant spike is tested; its feasibility requires the same reference target at every future time. The reward for (8) is $-\operatorname{Var}_t(R_T)$, so the direction of the equilibrium inequality is retained.
--
--   The implication relates preference-based and target-based formulations without asserting a converse. It is universal over stochastic state trajectories and complete families of actual SDE spike responses.
--
--   Differences from the source:
--   - reading: conditional mean–variance rewards and admissible policies → actual solution trajectories with finite conditional second moments, fixed common conditional versions and a complete response family; reason: finite conditional variance is necessary for the printed quotient to be defined; no unconditional L² bound, constant coefficients, constant preference or deterministic-policy restriction is imposed
--   - encoding: the conditional lower-limit inequality and Abar_t constraints for all future times → pointwise almost-sure epsilon inequality, with pathwise fixed-target constraints at every s in [t,T); reason: retains the extended-real liminf convention and all feasible spikes without a default-valued real liminf; the target is computed only from the reference trajectory
--   - generalization: target-equilibrium tests competitors feasible almost surely → the target-loss inequality also holds on each path where a globally admissible spike meets the fixed future targets; reason: the transfer uses only the initial-time mean constraint on that path; every source-feasible competitor is included
--   - generalization: equilibrium transfer in the feedback Markov setting described on p. 8 → transfer along arbitrary actual adapted SDE trajectories and complete response choices, without a Markov or SDE-uniqueness premise; reason: the source proof C.1 uses only conditional means, conditional variances, common current wealth and positive preference; specializing to the source Markov setting recovers its full implication
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. 10, Theorem 1; p. O–10, C.1

import Definitions.Def_LogMeanVar_Complete_Supplement_Equilibrium

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace LogMeanVar.Complete.Supplement

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns,
SSRN 3437268 (version of Aug 2019), p.10, Theorem 1; proof p.O–10 (C.1).
Every equilibrium for (7) transfers to (8) at its own adapted annual target.
Formalization Note: γ is time varying and adapted, since this theorem precedes
Assumption A. Actual scalar state/log-return SDE solutions and all admissible
constant spikes are retained. Conditional moments use bounded-truncation versions;
finite conditional second moments express that the source criterion is defined.
No uniqueness or Markov property is inferred from a state SDE. The conclusion tests
target feasibility at all future times and keeps the reference target fixed. -/
theorem theorem_1 {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (M : Model) (B W : ℝ≥0 → Ω → ℝ) (ρ : ℝ) (X R : ℝ → Ω → ℝ)
    (π : Policy) (γ : ℝ → Ω → ℝ) (Q : Responses Ω)
    (hM : M.Standing) (hNoise : CorrelatedNoise P F B W ρ)
    (hX : IsState M P F W X) (hAdapted : M.AdaptedAlong F X)
    (hγ : ∀ t ∈ Set.Ico 0 M.T,
      StronglyMeasurable[F t.toNNReal] (γ t) ∧ ∀ᵐ ω ∂P, 0 < γ t ω)
    (hEq : IsEquilibriumAlong M P F B X R π γ Q) :
    IsTargetEquilibriumAlong M P F B X R π Q (inducedTarget M P F R) := by sorry

end LogMeanVar.Complete.Supplement
