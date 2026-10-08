-- Prove2me | Theorems.Thm_NestedLogitVariants_LP_lp3_value_eq
-- name    : NestedLogitVariants.LP.lp3_value_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:21:27.647997+00:00
-- url     : https://prove2.me/theorems/ad355abf-eb3f-4a20-b702-627ad42ac3cc
-- title:
--   §2, p. 11 — problem (2) is equivalent to the linear program (3): its optimal value is Z*
-- statement:
--   Consider an instance of the nested logit assortment problem with at least one nest and at least one product, and let $(S_1^*, \dots, S_m^*)$ be an optimal assortment of problem (2), so $Z^* = \Pi(S_1^*, \dots, S_m^*)$. Then $Z^*$ is the optimal value of the linear program (3):
--
--   $$Z^* = \min\Big\{ x \;:\; \exists\, y,\ v_0 x \ge \sum_{i\in M} y_i,\ \ y_i \ge V_i(S_i)^{\gamma_i}(R_i(S_i) - x)\ \ \forall S_i \subseteq N,\ i \in M \Big\},$$
--
--   that is, $Z^*$ is feasible for (3) with a suitable $y$, and every feasible $x$ is at least $Z^*$. No positivity of $v_0$ is assumed; the paper notes that (3) continues to apply when $v_0 = 0$.
--
--   This is the linear-programming representation on which the approximation framework of the paper rests.
--
--   **Formalization Note** The minimum is stated with `IsLeast` on the set of feasible $x$. At least one nest and one product are assumed: with no nests, or no products, and $v_0 = v_{i0} = 0$, every $x$ is feasible for (3) and the claim fails, a degenerate instance the paper does not consider. The standing assumptions are those of §1: $v_0 \ge 0$, $v_{i0} \ge 0$, revenues ordered $r_{i1} \ge \dots \ge r_{in}$, together with the disclosed pins $v_{ij} > 0$ (the page allows zero-weight padding products, under which Proposition 2 of the paper fails), $r_{ij} \ge 0$ (revenues are prices) and $\gamma_i > 0$ (the page has $\gamma_i \ge 0$; its convention $V_i(\emptyset)^{\gamma_i} = 0$ when $v_{i0} = 0$ fails at $\gamma_i = 0$).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 11, §2, the derivation of (3) ("Therefore, problem (2) is equivalent to … x* = Z*")

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace NestedLogitVariants.LP

/-- §2, p. 11: problem (2) is equivalent to the linear program (3). If `S*` is an optimal
assortment, then `Z* = Π(S*)` is the least `x` for which some `y` makes `(x, y)` feasible for
(3), i.e. the optimal value of (3) is `Z*`. No positivity of `v_0` is assumed: the page states that
(3) "continues to apply when the preference weight `v_0` of the no purchase option is zero".
`Nonempty ι` and `0 < n` (at least one nest and one product) exclude the empty instance, in which
with `v_0 = 0` every `x` is feasible for (3). -/
theorem lp3_value_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) [Nonempty ι] (hn : 0 < n)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal I Sstar) :
    IsLeast {x | ∃ y, LP3Feasible I x y} (revenue I Sstar) := by sorry

end NestedLogitVariants.LP
