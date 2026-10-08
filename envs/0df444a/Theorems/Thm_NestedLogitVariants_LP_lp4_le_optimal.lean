-- Prove2me | Theorems.Thm_NestedLogitVariants_LP_lp4_le_optimal
-- name    : NestedLogitVariants.LP.lp4_le_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:21:39.603979+00:00
-- url     : https://prove2.me/theorems/fcc13b17-45fd-436d-9cf9-3a73b769077b
-- title:
--   §2, p. 12 — (4) relaxes (3), so its optimal value satisfies x̂ ≤ Z*
-- statement:
--   Let $\{A_{it} : t \in \mathcal T_i\}$ be candidate collections, let $(\hat x, \hat y)$ be an optimal solution of the linear program (4), and let $(S_1^*, \dots, S_m^*)$ be an optimal assortment of problem (2). Then
--
--   1. every feasible solution of (3) is feasible for (4), and
--   2. $$Z^* = \Pi(S_1^*, \dots, S_m^*) \ge \hat x.$$
--
--   Problem (4) imposes only a subset of the constraints of (3), so its optimal value cannot exceed that of (3), which is $Z^*$.
--
--   **Formalization Note** The standing assumptions are those of §1: $v_0 \ge 0$, $v_{i0} \ge 0$, revenues ordered $r_{i1} \ge \dots \ge r_{in}$, together with the disclosed pins $v_{ij} > 0$ (the page allows zero-weight padding products, under which Proposition 2 of the paper fails), $r_{ij} \ge 0$ (revenues are prices) and $\gamma_i > 0$ (the page has $\gamma_i \ge 0$; its convention $V_i(\emptyset)^{\gamma_i} = 0$ when $v_{i0} = 0$ fails at $\gamma_i = 0$).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 12, §2, paragraph "We observe that problem (4) includes only a subset of the constraints in problem (3) …"

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace NestedLogitVariants.LP

/-- §2, p. 12: problem (4) is a relaxation of problem (3) (every feasible point of (3) is feasible for
(4)), so the optimal value `x̂` of (4) satisfies `Z* = x* ≥ x̂`. -/
theorem lp4_le_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (A : ι → Set (Finset (Fin n))) (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I A xh yh)
    (Sstar : ι → Finset (Fin n)) (hSopt : IsOptimal I Sstar) :
    (∀ x y, LP3Feasible I x y → LP4Feasible I A x y) ∧ xh ≤ revenue I Sstar := by sorry

end NestedLogitVariants.LP
