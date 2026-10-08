-- Prove2me | Theorems.Thm_KellyReversibility_PartialBalance_insensitivity_product_form
-- name    : KellyReversibility.PartialBalance.insensitivity_product_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:22:58.028982+00:00
-- url     : https://prove2.me/theorems/6e7c3e8a-dee7-4c96-a3c2-2e13fa755f17
-- title:
--   Theorem 9.9 — partial balance of the reduced process gives the product form $\pi(\mathbf x)=\pi(\mathbf n)\prod_j P_j(x_j\mid n_j)$
-- statement:
--   Let $\mathbf x(t)$ be a spatial process with finite state space $\mathcal X_1\times\cdots\times\mathcal X_J$ and rates $q$, and for each site $j$ let $f_j:\mathcal X_j\to\mathcal N_j$ be onto, with $n_j=f_j(x_j)$ and $\mathbf n=f(\mathbf x)$. Suppose that for each $j$ the truncated process $x_j$ satisfies the two assumptions of p. 204: the rates $q(\mathbf x,T_j^y\mathbf x)$ depend on $\mathbf x_{G-j}$ only through $\mathbf n_{G-j}$, and its equilibrium distribution factors as $\pi(x_j;\mathbf x_{G-j})=\pi(n_j;\mathbf n_{G-j})P_j(x_j\mid n_j)$ (9.29), where each $P_j(\cdot\mid n_j)$ is a probability distribution on $\{x_j:f_j(x_j)=n_j\}$. Let the rates $q(\mathbf n,T_j^m\mathbf n)$ be defined by (9.31).
--
--   If there is a distribution $\pi(\mathbf n)$ (positive, summing to one over $\prod_j\mathcal N_j$) satisfying the partial balance equations (9.26) for each $j$, then the equilibrium distribution of $\mathbf x(t)$ is
--   $$\pi(\mathbf x)=\pi(\mathbf n)\prod_{j=1}^J P_j(x_j\mid n_j),\tag{9.32}$$
--   and it satisfies the partial balance equations
--   $$\pi(\mathbf x)\sum_{y\in\mathcal X_j}q(\mathbf x,T_j^y\mathbf x)=\sum_{y\in\mathcal X_j}\pi(T_j^y\mathbf x)q(T_j^y\mathbf x,\mathbf x)$$
--   for each $j$ and all $\mathbf x$.
--
--   This is the insensitivity mechanism of §9.4: the reduced description $\mathbf n$ keeps the equilibrium distribution $\pi(\mathbf n)$ whatever finer structure the attributes carry, provided partial balance holds.
--
--   **Formalization Note** The process is taken to be spatial for the complete graph on the sites, the setting the book adopts from p. 202 on (condition (ii) is then vacuous). Ontoness of $f_j$ is given by a section $s_j$, which also picks the representative used in (9.31). "The equilibrium distribution" is the unique positive normalized solution of the equilibrium equations.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 204, Theorem 9.9 (assumptions and (9.29)–(9.31) on pp. 203–204)

import Mathlib
import Definitions.Def_KellyReversibility_PartialBalance_Core
import Definitions.Def_KellyReversibility_PartialBalance_Spatial
import Definitions.Def_KellyReversibility_PartialBalance_Insensitivity

namespace KellyReversibility.PartialBalance

open Function

/-- **Theorem 9.9** (Kelly 1979, p. 204). Let `x(t)` be a spatial process on `∏_j 𝒳_j` whose
truncated processes satisfy the two assumptions of p. 204 for the reduction `n_j = f_j(x_j)`
with conditional distributions `P_j(x_j | n_j)`, and let the rates `q(n, T_j^m n)` be defined by
(9.31). If a distribution `π(n)` satisfies the partial balance equations (9.26) for each `j`,
then the equilibrium distribution of `x(t)` is `π(x) = π(n) ∏_j P_j(x_j | n_j)` (9.32), and it
satisfies the partial balance equations at every site. -/
theorem insensitivity_product_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X N : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (q : (∀ i, X i) → (∀ i, X i) → ℝ) (hsp : IsSpatialProcess (⊤ : SimpleGraph ι) q)
    (f : ∀ i, X i → N i) (s : ∀ i, N i → X i) (hs : ∀ (i : ι) (m : N i), f i (s i m) = m)
    (P : ∀ i, X i → ℝ) (hP0 : ∀ (i : ι) (y : X i), 0 ≤ P i y)
    (hP1 : ∀ (i : ι) (m : N i), ∑ y ∈ Finset.univ.filter (fun y => f i y = m), P i y = 1)
    (hA1 : ∀ j : ι, RatesFactorThrough q f j) (hA2 : ∀ j : ι, SufficientReduction q f P j)
    (πn : (∀ i, N i) → ℝ) (hπn_pos : ∀ n, 0 < πn n) (hπn_sum : ∑ n, πn n = 1)
    (hpb : ∀ (j : ι) (n : ∀ i, N i),
      πn n * (∑ m : N j, reducedRate q f P s n j m) =
        ∑ m : N j, πn (update n j m) * reducedRate q f P s (update n j m) j (n j)) :
    IsTheEquilibriumDist q (fun x => πn (reduce f x) * ∏ i, P i (x i)) ∧
      ∀ j : ι, SitePartialBalance (fun x => πn (reduce f x) * ∏ i, P i (x i)) q j := by sorry

end KellyReversibility.PartialBalance
