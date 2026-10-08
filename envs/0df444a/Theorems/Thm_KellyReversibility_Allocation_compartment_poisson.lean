-- Prove2me | Theorems.Thm_KellyReversibility_Allocation_compartment_poisson
-- name    : KellyReversibility.Allocation.compartment_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:08:33.933678+00:00
-- url     : https://prove2.me/theorems/d535071e-e9e8-489e-9e6d-0a1026ca3ec9
-- title:
--   Theorem 4.2 — at time t the compartment counts are independent Poisson with means να_j(t)
-- statement:
--   Particles arrive at a system of $J$ compartments in a Poisson stream of rate $\nu > 0$, the system being empty at time $0$, and move through the compartments independently of one another. Let $p_j(s)$ be the probability that an individual is in compartment $j$ a time $s$ after its arrival, and let $n_j(t)$ be the number of individuals in compartment $j$ at time $t > 0$. Then $n_1(t), \dots, n_J(t)$ are independent, and $n_j(t)$ has a Poisson distribution with mean $\nu\alpha_j(t)$, where
--   $$\alpha_j(t) = \int_0^t p_j(u)\,du;$$
--   that is,
--   $$P\big(n_j(t) = n\big) = e^{-\nu\alpha_j(t)}\frac{(\nu\alpha_j(t))^n}{n!}, \qquad n = 0, 1, 2, \dots$$
--
--   This gives the transient behaviour of the compartmental model. As $t \to \infty$ it recovers the equilibrium result that the counts are independent Poisson with means $\nu$ times the mean time an individual spends in each compartment.
--
--   **Formalization Note** "Individuals move independently" is formalized as in the proof on p. 115: the number $M$ of arrivals in $(0,t)$ is Poisson with mean $\nu t$; given $M$ the arrival instants are i.i.d. uniform on $(0,t)$; and an individual arriving at instant $u$ is in compartment $j$ at time $t$ with probability $p_j(t-u)$, independently across individuals. This is encoded by an i.i.d. sequence of (instant, location) pairs independent of $M$ (definition `IsCompartmentModel`). The $p_j$ are sub-probabilities: $\sum_j p_j(s) \le 1$, because individuals may leave the system. Independence is mutual independence of the $J$ counts.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 114–115, Theorem 4.2 (and the model of its proof)

import Mathlib
import Definitions.Def_KellyReversibility_Allocation_CompartmentModel

open MeasureTheory

namespace KellyReversibility.Allocation

theorem compartment_poisson {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ}
    {ν t : ℝ} {p : Fin J → ℝ → ℝ} {M : Ω → ℕ} {T : ℕ → Ω → ℝ}
    {Loc : ℕ → Ω → Fin J ⊕ Unit} (hmodel : IsCompartmentModel P ν t p M T Loc) :
    ProbabilityTheory.iIndepFun (fun j ω => compartmentCount M Loc j ω) P ∧
      ∀ (j : Fin J) (n : ℕ), P {ω | compartmentCount M Loc j ω = n}
        = ENNReal.ofReal (Real.exp (-(ν * alpha p j t)) * (ν * alpha p j t) ^ n
            / n.factorial) := by sorry

end KellyReversibility.Allocation
