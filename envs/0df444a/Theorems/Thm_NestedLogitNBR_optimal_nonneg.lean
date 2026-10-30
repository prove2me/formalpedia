-- Prove2me | Theorems.Thm_NestedLogitNBR_optimal_nonneg
-- name    : NestedLogitNBR.optimal_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:41:57.947981+00:00
-- url     : https://prove2.me/theorems/dc83b315-3e96-4fcd-b426-d0f4b56e146d
-- title:
--   Nonnegativity of the optimal solution $(\hat x,\hat y)$ of the nested-by-revenue problem (4)
-- statement:
--   There are $m$ nests $M=\{1,\dots,m\}$, each offering products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}\ge 0$, and the products of every nest are ordered so that $r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$. Nest $i$ has a dissimilarity parameter $\gamma_i\ge 0$, and $v_0\ge 0$ is the preference weight of choosing no nest. As in Section 4 of the paper the no-purchase weights inside the nests are $v_{i0}=0$, so $V_i(S)=\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$. The nested-by-revenue assortments are $N_{ij}=\{1,\dots,j\}$ for $j\in N_+=\{0,1,\dots,n\}$, with $N_{i0}=\emptyset$.
--
--   Let $(\hat x,\hat y)$ be an optimal solution of problem (4) with the nested-by-revenue candidate assortments $\{N_{ij}:j\in N_+\}$. Then
--
--   $$
--   \hat x\ge0\qquad\text{and}\qquad \hat y_i\ge0\ \ \text{for all } i\in M.
--   $$
--
--   This is the first step of the proof of Theorem 7: the constraint for $N_{i0}=\emptyset$ gives $\hat y_i\ge0$, and these signs are what allow the factor $\alpha\ge1$ to be moved onto $\hat x$ and $\hat y$.
--
--   Differences from the source:
--   - reading: revenues r_ij with no stated sign → r_ij ≥ 0; reason: revenues are prices; the proof uses x̂ ≥ 0 and Σ_{k≤j} r_ik v_ik ≥ Σ_{k≤j−1} r_ik v_ik; with negative revenues the printed Theorem 7 fails on fully defined data (E2: nest 1 with γ=2, r=(−1,−2), v=(1,1), nest 2 with γ=0.01, r=(2,1), v=(1,1), v_0=1: every term of (6) is defined, (6) = 0.755, x̂ = 1, and (0.755 x̂, 0.755 ŷ) is infeasible for (3))
--   - reading: V_i(S)^{γ_i} (and (Σ_j v_ij z_ij)^{γ_i} in (7), (8)) at total weight 0 → 0 when the weight is 0, Real.rpow otherwise; reason: the paper uses V_i(∅)^{γ_i}(R_i(∅) − x̂) = 0 (p. 41) and an assortment of total weight 0 is never chosen (p. 7); Real.rpow gives 0^0 = 1 at γ_i = 0, which the model allows
--   - generalization: standing assumption of §4 (p. 16): γ_i > 1 for some i ∈ M → not assumed; reason: the inequality does not use it; every instance satisfying it is covered
--   - encoding: v_i0 = 0 (§4); products {1,…,n}; N_ij = {1,…,j}, j ∈ N_+; S_i ⊂ N; optimal solution of (4); R_i(∅) = 0 → prefWeight without v_i0; Fin n, 0-based; nbr j; every Finset (Fin n); FeasibleNBR with least x (IsOptimalNBR); x/0 = 0; reason: Lean conventions; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), App. A.1 (proof of Theorem 7), p. 41, unnumbered

import Mathlib
import Definitions.Def_NestedLogitNBR_IsOptimalNBR

namespace NestedLogitNBR

/-- **Nonnegativity of the optimal solution of the nested-by-revenue problem (4).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), App. A.1 (proof of Theorem 7), p. 41, unnumbered: "this solution satisfies the second set
of constraints for nest `i` and the nested-by-revenue assortment `N_i0 = ∅`. Noting that
`V_i(∅) = 0`, it follows that `ŷ_i ≥ 0` for all `i ∈ M`. In this case, the first constraint
in problem (4) implies that `x̂ ≥ 0`."

Standing hypotheses (pp. 7, 16): `v_0 ≥ 0`, `v_ij ≥ 0`, revenues `r_ij ≥ 0` ordered
`r_i1 ≥ … ≥ r_in` in every nest, `γ_i ≥ 0`, `v_i0 = 0`.

**Formalization Note.** For `v_0 = 0` the first constraint gives no bound on `x̂`; the claim
`x̂ ≥ 0` then comes from optimality, as stated. -/
theorem optimal_nonneg {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ)
    (hv0 : 0 ≤ v0) (hv : ∀ i j, 0 ≤ v i j) (hr : ∀ i j, 0 ≤ r i j)
    (hord : ∀ i, Antitone (r i)) (hγ : ∀ i, 0 ≤ γ i)
    (x : ℝ) (y : Fin m → ℝ) (hopt : IsOptimalNBR v0 r v γ x y) :
    0 ≤ x ∧ ∀ i, 0 ≤ y i := by sorry

end NestedLogitNBR
