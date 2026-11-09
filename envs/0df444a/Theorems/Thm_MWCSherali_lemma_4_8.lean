-- Prove2me | Theorems.Thm_MWCSherali_lemma_4_8
-- name    : MWCSherali.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:17:19.239198+00:00
-- url     : https://prove2.me/theorems/030252d6-34c0-4145-805d-80cca83bd655
-- title:
--   Lemma 4.8 — Equation (19) is feasible for the continuous Flow LP
-- statement:
--   Assume $\beta>0$, $\tfrac12<\alpha\le1-3\beta$ and (17), and let $C$ be given by (18). Then the measures
--
--   $$F_{a,i}=\sum_RF^R_{a,i},\qquad B_i=\sum_RB^R_i\qquad(i\neq a\in[4]),\tag{19}$$
--
--   summed over all corners, simplex edges, tubes and the central region, together with the exit measures $\nu_a$, form a feasible solution of (Continuous-Flow-LP) for $k=4$.
--
--   Differences from the source:
--   - encoding: φ ∈ C^{(1)}(Δ_k), continuously differentiable on Δ_k → ContDiff ℝ 1 φ on all of ℝ^k; reason: the constraints use only values on Δ_k and derivatives tangent to Δ_k, and every C¹ function on Δ_k agrees there with a global C¹ function
--   - encoding: Borel measures on Δ_k, probability measures on Γ_a → measures on Fin k → ℝ giving the complement of Δ_k (resp. Γ_a) measure 0; reason: Lean convention; the same measures
--   - encoding: nonnegative capacity measures B_i → B_i required to be finite measures; reason: an infinite capacity has objective ∞ and changes no infimum; it makes every integral a genuine one
--   - encoding: indices a, b, i ∈ [4] (1-based) → Fin 4 (0-based); reason: Lean convention
--   - encoding: densities such as Cβ(w − 1 + α), Cβ/(t_i + t_j) → ENNReal.ofReal of the density; reason: the densities are nonnegative on their supports under the standing assumptions
--   - reading: Lemma 4.8 (stated without hypotheses, within §4.5) → hypotheses of Lemma 4.6 on α, β (β > 0, 1/2 < α ≤ 1 − 3β, (17)); C fixed by (18); reason: the construction uses Lemma 4.6's density vectors and the normalization (18)
--   - encoding: (19) for i ≠ a; the solution's exit measures → Ftot α β a i (used for a ≠ i), Btot α β i and ν_a = nuZ α β C; reason: the paper's ν_a of Lemma 4.7 with C from (18)
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.8, p.41; (18)–(19), p.41

import Mathlib
import Definitions.Def_MWCSherali_ContFlowFeasible
import Definitions.Def_MWCSherali_Ftot
import Definitions.Def_MWCSherali_Btot
import Definitions.Def_MWCSherali_nuZ
import Definitions.Def_MWCSherali_Cnorm

namespace MWCSherali

/-- **Lemma 4.8 (feasibility of the construction).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.8, p.41:
"Equation (19) defines a feasible solution to (Continuous-Flow-LP)."

The solution is `F_{a,i} = ∑_R F^R_{a,i}` (`Ftot`), `B_i = ∑_R B^R_i` (`Btot`) and the exit
measures `ν_a` (`nuZ`), with `C` given by (18) (`Cnorm`).

**Formalization Note.** Hypotheses: Lemma 4.6's assumptions on `α, β` (`β > 0`,
`1/2 < α ≤ 1 − 3β`, (17)), under which the density vectors of the central region are those of
Lemma 4.6; `C` is fixed by (18). No parametrization of `α, β` (the `λ` of §4.6) is assumed. -/
theorem lemma_4_8 (α β : ℝ) (hβ : 0 < β) (hα : 1 / 2 < α) (hαβ : α ≤ 1 - 3 * β)
    (h17 : 4 * (1 - α) ^ 2 - 24 * (1 - α) * β + 6 * β ^ 2 + 12 * β - 1 = 0) :
    ContFlowFeasible 4 (Ftot α β) (Btot α β) (nuZ α β (Cnorm α β)) := by sorry

end MWCSherali
