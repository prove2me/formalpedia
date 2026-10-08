-- Prove2me | Theorems.Thm_KellyReversibility_Allocation_compartment_pgf
-- name    : KellyReversibility.Allocation.compartment_pgf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:08:29.427779+00:00
-- url     : https://prove2.me/theorems/02b6938a-e095-415f-8e0a-491daee12d29
-- title:
--   Proof of Theorem 4.2, p. 115 — E(∏ z_j^{n_j(t)}) = ∏ exp[−(1 − z_j)να_j(t)]
-- statement:
--   In the compartmental model with Poisson arrivals of rate $\nu$ observed at time $t > 0$ (system empty at time $0$, individuals moving independently, $p_j(s)$ the probability of being in compartment $j$ a time $s$ after arrival), let $n_j(t)$ be the number of individuals in compartment $j$ at time $t$ and $\alpha_j(t) = \int_0^t p_j(u)\,du$. Then for all $z_1, \dots, z_J \in [0, 1]$ the joint probability generating function is
--   $$E\big(z_1^{n_1(t)} z_2^{n_2(t)} \cdots z_J^{n_J(t)}\big) = \prod_{j=1}^{J} \exp\big[-(1 - z_j)\,\nu\,\alpha_j(t)\big].$$
--
--   This product form of the generating function is what identifies the counts as independent Poisson variables in Theorem 4.2.
--
--   **Formalization Note** The model is the definition `IsCompartmentModel` (Poisson number $M$ of arrivals in $(0,t)$, independent of an i.i.d. sequence of arrival instants uniform on $(0,t)$ and locations at time $t$). The generating function is taken for $z_j \in [0,1]$, where the integrand is bounded by $1$; this range determines the joint law.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 115, proof of Theorem 4.2 (final display)

import Mathlib
import Definitions.Def_KellyReversibility_Allocation_CompartmentModel

open MeasureTheory

namespace KellyReversibility.Allocation

theorem compartment_pgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ}
    {ν t : ℝ} {p : Fin J → ℝ → ℝ} {M : Ω → ℕ} {T : ℕ → Ω → ℝ}
    {Loc : ℕ → Ω → Fin J ⊕ Unit} (hmodel : IsCompartmentModel P ν t p M T Loc)
    (z : Fin J → ℝ) (hz0 : ∀ j, 0 ≤ z j) (hz1 : ∀ j, z j ≤ 1) :
    ∫ ω, ∏ j, z j ^ compartmentCount M Loc j ω ∂P
      = ∏ j, Real.exp (-(1 - z j) * ν * alpha p j t) := by sorry

end KellyReversibility.Allocation
