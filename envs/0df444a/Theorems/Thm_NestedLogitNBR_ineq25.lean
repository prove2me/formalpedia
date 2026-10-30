-- Prove2me | Theorems.Thm_NestedLogitNBR_ineq25
-- name    : NestedLogitNBR.ineq25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:48:41.848365+00:00
-- url     : https://prove2.me/theorems/3bc6b4c2-e866-4366-8797-1c2b2822288a
-- title:
--   Inequality (25) — Case 2 ($k=1$) of the proof of Theorem 7
-- statement:
--   There are $m$ nests $M=\{1,\dots,m\}$, each offering products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}\ge 0$, and the products of every nest are ordered so that $r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$. Nest $i$ has a dissimilarity parameter $\gamma_i\ge 0$, and $v_0\ge 0$ is the preference weight of choosing no nest. As in Section 4 of the paper the no-purchase weights inside the nests are $v_{i0}=0$, so $V_i(S)=\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$. The nested-by-revenue assortments are $N_{ij}=\{1,\dots,j\}$ for $j\in N_+=\{0,1,\dots,n\}$, with $N_{i0}=\emptyset$.
--
--   Let $(\hat x,\hat y)$ be an optimal solution of problem (4) with the nested-by-revenue candidates $\{N_{ij}:j\in N_+\}$, let $\alpha=\max\{1,(6)\}$, and let $i\in M$, $\rho\in[0,1]$. Then
--
--   $$
--   \alpha\,\hat y_i\ \ge\ (v_{i1}\rho)^{\gamma_i}\left[\frac{r_{i1}v_{i1}\rho}{v_{i1}\rho}-\alpha\,\hat x\right].\tag{25}
--   $$
--
--   The right side is the objective of (8) at $x=\alpha\hat x$ evaluated at the threshold vector $z_1=\rho$, $z_2=\dots=z_n=0$; with (24) and Lemma 6 this shows that $(\alpha\hat x,\alpha\hat y)$ satisfies the nest constraints of (7).
--
--   Differences from the source:
--   - reading: α, the expression (6): max over i ∈ M, j = 2,…,n of the bracketed minimum → factor6 = max{1, (6)}, Lean's x/0 = 0 inside the terms, and 1 for n ≤ 1; reason: (6) is 0/0 on data the model allows (zero-weight padding, p. 7; zero revenues, as in the reduction of Theorem 5, p. 18) and the paper does not say what it is then; the bare maximum with x/0 = 0 makes the statement false (E1: nest 1 with γ=2, r=(0,0), v=(1,1), nest 2 with γ=0.01, r=(2,1), v=(1,1), v_0=1 satisfies every assumption of §4; all of nest 1's terms are 0/0, the Lean value of the bare maximum is 0.755, x̂ = 1, and (0.755 x̂, 0.755 ŷ) is infeasible for (3)); wherever every term is defined and some γ_i > 1, Lemma 14 gives (6) ≥ 1 so max{1, (6)} = (6); α ≥ 1 is necessary whenever x̂ > 0
--   - generalization: standing assumption of §4 (p. 16): γ_i > 1 for some i ∈ M → not assumed; every γ_i ≥ 0; reason: with α = max{1, (6)} the assumption is used only through Lemma 14 to get α ≥ 1, which the reading builds in; under the assumption the statement specializes to the paper's wherever (6) is defined
--   - reading: revenues r_ij with no stated sign → r_ij ≥ 0; reason: revenues are prices; the proof uses x̂ ≥ 0 and Σ_{k≤j} r_ik v_ik ≥ Σ_{k≤j−1} r_ik v_ik; with negative revenues the printed Theorem 7 fails on fully defined data (E2: nest 1 with γ=2, r=(−1,−2), v=(1,1), nest 2 with γ=0.01, r=(2,1), v=(1,1), v_0=1: every term of (6) is defined, (6) = 0.755, x̂ = 1, and (0.755 x̂, 0.755 ŷ) is infeasible for (3))
--   - reading: V_i(S)^{γ_i} (and (Σ_j v_ij z_ij)^{γ_i} in (7), (8)) at total weight 0 → 0 when the weight is 0, Real.rpow otherwise; reason: the paper uses V_i(∅)^{γ_i}(R_i(∅) − x̂) = 0 (p. 41) and an assortment of total weight 0 is never chosen (p. 7); Real.rpow gives 0^0 = 1 at γ_i = 0, which the model allows
--   - encoding: the right side (v_i1 ρ)^{γ_i}[r_i1 v_i1 ρ/(v_i1 ρ) − α x̂] → fracObj at threshold k ρ with k.val = 0, level α x̂; reason: the two are equal when v_i1 ρ > 0; at v_i1 ρ = 0 (0/0 in the paper) fracObj gives 0, its convention
--   - encoding: v_i0 = 0 (§4); products {1,…,n}; N_ij = {1,…,j}, j ∈ N_+; S_i ⊂ N; optimal solution of (4); R_i(∅) = 0 → prefWeight without v_i0; Fin n, 0-based; nbr j; every Finset (Fin n); FeasibleNBR with least x (IsOptimalNBR); x/0 = 0; reason: Lean conventions; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), App. A.1 (proof of Theorem 7, Case 2), p. 43, eq. (25)

import Mathlib
import Definitions.Def_NestedLogitNBR_IsOptimalNBR
import Definitions.Def_NestedLogitNBR_factor6
import Definitions.Def_NestedLogitNBR_fracObj
import Definitions.Def_NestedLogitNBR_threshold

namespace NestedLogitNBR

/-- **Inequality (25) (Case 2, `k = 1`, of the proof of Theorem 7).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), App. A.1, p. 43, eq. (25): `α ŷ_i ≥ (v_i1 ρ)^{γ_i} [ r_i1 v_i1 ρ / (v_i1 ρ) − α x̂ ]`,
where `(x̂, ŷ)` is an optimal solution of problem (4) with the nested-by-revenue candidates
`{N_ij : j ∈ N_+}`, `α` is the expression (6) and `ρ ∈ [0, 1]`.

Standing hypotheses (pp. 7, 16): `v_0 ≥ 0`, `v_ij ≥ 0`, revenues `r_ij ≥ 0` ordered
`r_i1 ≥ … ≥ r_in` in every nest, `γ_i ≥ 0`, `v_i0 = 0`.

**Formalization Note.** The right side of (25) is the objective of (8) at `x = α x̂` evaluated
at the threshold vector `z_i1 = ρ`, `z_i2 = … = z_in = 0`; it is written as `fracObj` at
`threshold k ρ` with `k.val = 0` (Lean `k : Fin n` is the paper's `k.val + 1`), which also
covers `v_i1 ρ = 0` with the convention of `fracObj` (value `0`). `α` is
`factor6 = max{1, (6)}`. -/
theorem ineq25 {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ)
    (hv0 : 0 ≤ v0) (hv : ∀ i j, 0 ≤ v i j) (hr : ∀ i j, 0 ≤ r i j)
    (hord : ∀ i, Antitone (r i)) (hγ : ∀ i, 0 ≤ γ i)
    (x : ℝ) (y : Fin m → ℝ) (hopt : IsOptimalNBR v0 r v γ x y)
    (i : Fin m) (k : Fin n) (hk : k.val = 0) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    fracObj r v γ i (threshold k ρ) (factor6 r v γ * x) ≤ factor6 r v γ * y i := by sorry

end NestedLogitNBR
