-- Prove2me | Theorems.Thm_MultiStageAlloc_proposition_3
-- name    : MultiStageAlloc.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:44.730708+00:00
-- url     : https://prove2.me/theorems/e9439d1e-d80e-4516-9308-fccbceccfa0c
-- title:
--   Proposition 3 — KKT conditions for the stage program
-- statement:
--   Let $1\le k\le K$, let $y\in[0,1]^V$, let $x^*$ be an optimal solution of the stage program, and write $v$ for its objective value. Then the max-min and min-max of the Lagrangian coincide and equal $v$:
--   $$
--   \max_x\min_{\lambda,\theta,\gamma}\mathcal L_k=\min_{\lambda,\theta,\gamma}\max_x\mathcal L_k=\min_{\lambda,\theta,\gamma}\mathcal L_k(x^*,\lambda,\theta,\gamma)=v,
--   $$
--   which is stated by: $\mathcal L_k(x^*,m)\ge v$ for all dual feasible $m$, and some dual feasible $m^*$ has $\mathcal L_k(x^*,m^*)=v$ and $\mathcal L_k(z,m^*)\le v$ for every allocation $z$ of stage $k$.
--
--   Moreover, every dual feasible $(\lambda^*,\theta^*,\gamma^*)$ solving the min-max, i.e. having $\mathcal L_k(z,\lambda^*,\theta^*,\gamma^*)\le v$ for all $z$, satisfies:
--
--   1. **Stationarity.** For $(i,j)\in E_k$: $w_j(1-\mathrm{slope}_k(\text{level of }j))-\lambda^*_i-\theta^*_j/n_j+\gamma^*_{ij}=0$.
--   2. **Complementary slackness.** $\gamma^*_{ij}=0$ or ($\gamma^*_{ij}>0$ and $x^*_{ij}=0$); $\lambda^*_i=0$ or ($\lambda^*_i>0$ and $\sum_jx^*_{ij}=1$); $\theta^*_j=0$ or ($\theta^*_j>0$ and the level of $j$ is $1$).
--
--   These conditions drive the structural decomposition of Proposition 2, and at $k=K$ they provide the optimal dual of the last-stage LP.
--
--   Differences from the source:
--   - generalization: capacities n_j = 1 "without the loss of generality" (p.12), and Algorithm 1 printed only for n_j = 1 → every real n_j > 0, with normalized levels y_j + Σ_i x_ij / n_j and the coefficient n_j in the regularizer and in the dual objective; reason: at n_j = 1 this is the printed text character for character, so the statement specializes to the source
--   - generalization: |U_k| ≥ 1 (p.12) → a batch may be empty, and U, V may be empty; reason: instances with nonempty batches are a subclass, and nothing in the proof uses nonemptiness
--   - reading: no cardinality assumption on U and V is printed → U and V are finite (Fintype); reason: the program and the LP are finite sums on the page, and footnote 8 and "no further assumptions" concern batch sizes
--   - encoding: x_k ∈ ℝ^{E_k} → x : U → V → ℝ vanishing off E_k; reason: sums over U and V are then the printed sums over E_k; same instances
--   - reading: "the optimal solution" of the stage program → every optimal solution; reason: the optimum need not be unique (p.17 "unique" is a slip: two online vertices sharing one offline vertex give several optima), and every optimum is the strongest reading
--   - generalization: y is the current vector of levels of Algorithm 1 → any y ∈ [0,1]^V; reason: the levels of a run lie in [0,1], so the source case is an instance, and the proof uses nothing else about y
--   - reading: L_k with F_k and x unconstrained (Definition 2), F_k defined on [0,1] → L_k with the C¹ convex extension F̃_k of F_k, x ∈ ℝ^{E_k} unconstrained; reason: max_x has no meaning off [0,1]; the polynomial extension is not concave, and restricting x to the domain makes the moreover clause false (y_j = 1, θ_j = 5 is a min-max solution where stationarity fails)
--   - encoding: the chain of equalities of max min and min max → the common value v and its attainment, stated by inequalities; reason: a real sSup or sInf of L over unbounded sets would return a default value; the inequalities give the three equalities in the extended reals
--   - reading: "(together with x*_k) are the solutions of the above minmax/maxmin" → m* with L(z, m*) ≤ v for all z; reason: this is what m* solving the min-max says when its value is v, the weakest hypothesis under which the printed conclusion holds
--   - encoding: ∂L_k/∂x_ij (x*, λ*, θ*, γ*) = 0 → the derivative written out, w_j(1 − slope(level_j)) − λ_i − θ_j/n_j + γ_ij = 0; reason: F̃_k has derivative slope (proved in the sanity file); same condition
--   - generalization: complementary slackness only for i, j with (i, j) ∈ E_k → for λ all i ∈ U_k and for θ all j ∈ V; reason: the source case is a subset
--   - reading: min over λ, θ, γ with no printed range, and (Dual feasibility) listed among the consequences → the multipliers range over dual feasible m (DualNonneg), which is a hypothesis of the moreover clause and not a conclusion; reason: an unrestricted min is −∞ as soon as a constraint is slack at x*, so the printed min can only be over nonnegative multipliers, and dual feasibility of a minimizer is then its range and nothing more
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Proposition 3, p.39

import Mathlib
import Definitions.Def_MultiStageAlloc_Lagrangian

namespace MultiStageAlloc

/-- **Proposition 3 (KKT Conditions for Multi-stage Polynomial Regularized Matching).** Feng &
Niazadeh, arXiv:2211.16581v1, p.39, for every `1 ≤ k ≤ K`, levels `y ∈ [0, 1]^V` and optimal
solution `x` of (P^VWM_k).

The first two conjuncts are the printed chain of equalities, with `v = stageObj x` the common value
stated directly: for all multipliers, `L(x, m) ≥ v` (so `min_m L(x, m)` is at least `v`); and some
multipliers `m*` have `L(x, m*) = v` and `L(z, m*) ≤ v` for every `z ∈ ℝ^{E_k}` (so the three values
are all `v`, and all attained). The third conjunct is the "moreover": every `m*` solving
`min_m max_z L` has stationarity and complementary slackness.

**Formalization Note.** Stationarity is written out: `∂L/∂x_ij = w_j (1 - slope(level_j)) - λ_i - θ_j
/ n_j + γ_ij`. No real `sSup`/`sInf` of `L` appears, since those sets can be unbounded. `F̃_k` replaces
`F_k` in `L`, see `lagrangian`. The dual variable `θ_j` dualizes `y_j + ∑_i x_ij / n_j ≤ 1`. -/
theorem proposition_3 {U V : Type*} [Fintype U] [Fintype V] {K : ℕ} (I : Instance U V K)
    (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) (y : V → ℝ) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1)
    (x : U → V → ℝ) (hx : IsStageOptimal I k y x) :
    (∀ (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ), DualNonneg I k lam θ γ →
      stageObj I k y x ≤ lagrangian I k y x lam θ γ) ∧
    (∃ (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ), DualNonneg I k lam θ γ ∧
      lagrangian I k y x lam θ γ = stageObj I k y x ∧
      ∀ z, StageSupported I k z → lagrangian I k y z lam θ γ ≤ stageObj I k y x) ∧
    (∀ (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ), DualNonneg I k lam θ γ →
      (∀ z, StageSupported I k z → lagrangian I k y z lam θ γ ≤ stageObj I k y x) →
      (∀ i j, I.edge i j → I.batch i = k →
        I.w j * (1 - slope K k (level I y x j)) - lam i - θ j / I.cap j + γ i j = 0) ∧
      (∀ i j, I.edge i j → I.batch i = k → γ i j = 0 ∨ (0 < γ i j ∧ x i j = 0)) ∧
      (∀ i, I.batch i = k → lam i = 0 ∨ (0 < lam i ∧ ∑ j, x i j = 1)) ∧
      (∀ j, θ j = 0 ∨ (0 < θ j ∧ level I y x j = 1))) := by sorry

end MultiStageAlloc
