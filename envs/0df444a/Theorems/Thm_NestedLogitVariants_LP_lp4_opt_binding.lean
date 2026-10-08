-- Prove2me | Theorems.Thm_NestedLogitVariants_LP_lp4_opt_binding
-- name    : NestedLogitVariants.LP.lp4_opt_binding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:21:24.018205+00:00
-- url     : https://prove2.me/theorems/ff61c410-5fba-4fe4-9f7d-da4db34bb1e1
-- title:
--   §2, p. 12 — at an optimum of (4) the first constraint binds and x̂ = Π(Ŝ_1, …, Ŝ_m)
-- statement:
--   Assume $v_0 > 0$. Let $(\hat x, \hat y)$ be an optimal solution of the linear program (4) with candidate collections $\{A_{it} : t \in \mathcal T_i\}$, and for every nest $i$ let $\hat S_i$ be a member of the collection of nest $i$ that maximizes $V_i(S_i)^{\gamma_i}(R_i(S_i) - \hat x)$ over that collection. Then
--
--   $$v_0\,\hat x = \sum_{i\in M} V_i(\hat S_i)^{\gamma_i}\big(R_i(\hat S_i) - \hat x\big) \qquad\text{and}\qquad \hat x = \Pi(\hat S_1, \dots, \hat S_m).$$
--
--   So the expected revenue of the assortment stitched together from the maximizers is exactly the optimal value of (4).
--
--   **Formalization Note** The hypothesis $v_0 > 0$ is added. The page allows $v_0 = 0$, but its step "solving for $\hat x$" divides by $v_0 + \sum_i V_i(\hat S_i)^{\gamma_i}$, which can vanish then, and the conclusion fails: one nest, $v_{10} = 0$, $\gamma_1 = 1$, one product with $r_{11} = v_{11} = 1$, candidates $\{\emptyset, \{1\}\}$; then $\hat x = 1$ and $\hat S_1 = \emptyset$ is a maximizer, but $\Pi(\emptyset) = 0$. The standing assumptions are those of §1: $v_0 \ge 0$, $v_{i0} \ge 0$, revenues ordered $r_{i1} \ge \dots \ge r_{in}$, together with the disclosed pins $v_{ij} > 0$ (the page allows zero-weight padding products, under which Proposition 2 of the paper fails), $r_{ij} \ge 0$ (revenues are prices) and $\gamma_i > 0$ (the page has $\gamma_i \ge 0$; its convention $V_i(\emptyset)^{\gamma_i} = 0$ when $v_{i0} = 0$ fails at $\gamma_i = 0$).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 12, §2, paragraph "We will now argue that the constraint above must be satisfied as equality …"

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace NestedLogitVariants.LP

/-- §2, p. 12: at an optimal solution `(x̂, ŷ)` of (4), the first constraint binds with the
maximizers `Ŝ_i` of (5): `v_0 x̂ = ∑_i V_i(Ŝ_i)^{γ_i} (R_i(Ŝ_i) − x̂)`, and hence
`x̂ = Π(Ŝ_1, …, Ŝ_m)`. Pinned `0 < v_0` (the step "solving for x̂" divides by
`v_0 + ∑_i V_i(Ŝ_i)^{γ_i}`, which can vanish when `v_0 = 0`). -/
theorem lp4_opt_binding {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hv0 : 0 < I.v0)
    (A : ι → Set (Finset (Fin n))) (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I A xh yh)
    (Sh : ι → Finset (Fin n)) (hSmem : ∀ i, Sh i ∈ A i)
    (hSmax : ∀ i, ∀ S ∈ A i,
      nestWeight I i S * (R I i S - xh) ≤ nestWeight I i (Sh i) * (R I i (Sh i) - xh)) :
    I.v0 * xh = ∑ i, nestWeight I i (Sh i) * (R I i (Sh i) - xh) ∧ xh = revenue I Sh := by sorry

end NestedLogitVariants.LP
