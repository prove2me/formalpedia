-- Prove2me | Theorems.Thm_NestedLogitVariants_LP_theorem_1
-- name    : NestedLogitVariants.LP.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:21:51.550926+00:00
-- url     : https://prove2.me/theorems/6d36b854-cac7-4110-9f7f-3c121ea02b91
-- title:
--   Theorem 1, p. 13 — if (αx̂, βŷ) is feasible for (3), the assortment of (5) earns within a factor α: αẐ ≥ Z* ≥ Ẑ
-- statement:
--   Assume $v_0 > 0$. Let $\{A_{it} : t \in \mathcal T_i\}$ be candidate collections of assortments for the nests, let $(\hat x, \hat y)$ be an optimal solution of the linear program (4), and for every nest $i$ let $\hat S_i$ be an optimal solution of
--
--   $$\max_{S_i \in \{A_{it} : t \in \mathcal T_i\}} V_i(S_i)^{\gamma_i}\big(R_i(S_i) - \hat x\big). \tag{5}$$
--
--   If $(\alpha \hat x, \beta \hat y)$ is feasible for the linear program (3) for some real $\alpha$ and $\beta$, then, writing $\hat Z = \Pi(\hat S_1, \dots, \hat S_m)$ and $Z^*$ for the optimal value of problem (2),
--
--   $$\alpha \hat Z \ \ge\ Z^* \ \ge\ \hat Z.$$
--
--   So the revenue of the assortment stitched together from the candidate collections deviates from the optimum by no more than a factor of $\alpha$. This is the general approximation framework of the paper: the performance guarantees of Theorems 7, 10, 11 and 12 are obtained by exhibiting candidate collections for which $(\alpha\hat x, \beta\hat y)$ is feasible for (3).
--
--   **Formalization Note** $Z^*$ is $\Pi(S^*)$ for an arbitrary optimal assortment $S^*$ (one always exists, since there are finitely many assortments). The hypothesis $v_0 > 0$ is added: the paper allows $v_0 = 0$, but the theorem is false then. Take one nest with $v_{10} = 0$, $\gamma_1 = 1$, one product with $r_{11} = v_{11} = 1$, and candidates $\{\emptyset, \{1\}\}$; then $(\hat x, \hat y) = (1, 0)$ is optimal for (4), $\hat S_1 = \emptyset$ solves (5), $(\hat x, \hat y)$ is feasible for (3) with $\alpha = \beta = 1$, and $\hat Z = 0 < Z^* = 1$. The paper's derivation divides by $v_0 + \sum_i V_i(\hat S_i)^{\gamma_i}$, which vanishes in this instance. No sign condition is placed on $\alpha$ or $\beta$. The standing assumptions are those of §1: $v_0 \ge 0$, $v_{i0} \ge 0$, revenues ordered $r_{i1} \ge \dots \ge r_{in}$, together with the disclosed pins $v_{ij} > 0$ (the page allows zero-weight padding products, under which Proposition 2 of the paper fails), $r_{ij} \ge 0$ (revenues are prices) and $\gamma_i > 0$ (the page has $\gamma_i \ge 0$; its convention $V_i(\emptyset)^{\gamma_i} = 0$ when $v_{i0} = 0$ fails at $\gamma_i = 0$).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 13, Theorem 1 and display (5)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace NestedLogitVariants.LP

/-- Theorem 1, p. 13. Let `(x̂, ŷ)` be an optimal solution of (4) and `Ŝ_i` an optimal solution of
(5), `max_{S_i ∈ A_i} V_i(S_i)^{γ_i} (R_i(S_i) − x̂)`, for every nest `i`. If `(α x̂, β ŷ)` is
feasible for (3), then `α Ẑ ≥ Z* ≥ Ẑ` with `Ẑ = Π(Ŝ_1, …, Ŝ_m)` and `Z* = Π(S*)` for any optimal
`S*` of (2). Pinned `0 < v_0`: the statement is false for `v_0 = 0` (one nest, `v_{10} = 0`,
`γ_1 = 1`, `r_{11} = v_{11} = 1`, `A_1 = {∅, {1}}`, `x̂ = 1`, `Ŝ_1 = ∅`, `α = β = 1`). -/
theorem theorem_1 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hv0 : 0 < I.v0)
    (A : ι → Set (Finset (Fin n))) (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I A xh yh)
    (Sh : ι → Finset (Fin n)) (hSmem : ∀ i, Sh i ∈ A i)
    (hSmax : ∀ i, ∀ S ∈ A i,
      nestWeight I i S * (R I i S - xh) ≤ nestWeight I i (Sh i) * (R I i (Sh i) - xh))
    (α β : ℝ) (hfeas : LP3Feasible I (α * xh) (β • yh)) :
    ∀ Sstar, IsOptimal I Sstar →
      revenue I Sstar ≤ α * revenue I Sh ∧ revenue I Sh ≤ revenue I Sstar := by sorry

end NestedLogitVariants.LP
