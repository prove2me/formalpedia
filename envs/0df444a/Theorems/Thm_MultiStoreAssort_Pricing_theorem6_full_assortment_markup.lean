-- Prove2me | Theorems.Thm_MultiStoreAssort_Pricing_theorem6_full_assortment_markup
-- name    : MultiStoreAssort.Pricing.theorem6_full_assortment_markup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:22.595331+00:00
-- url     : https://prove2.me/theorems/8ed708ba-b948-4db5-a635-138f56955503
-- title:
--   Theorem 6, PDF p. 28 — under SMR, the full assortment in every store at prices θ*ᵢ + 1/βᵢₖ solves the joint problem (13)
-- statement:
--   A seller runs $m$ stores and sells $n$ products. A fraction $\lambda_i\ge0$ of customers visits store $i$, $\sum_i\lambda_i=1$. A store-$i$ customer who buys product $k$ from store $j$ at store $j$'s price $p_{jk}$ has utility $\alpha_{ik}-\beta_{ik}p_{jk}-c^k_{ij}$ plus Gumbel noise, with $\alpha_{ik}>0$, $\beta_{ik}>0$, $c^k_{ij}\ge 0$ and $c^k_{ii}=0$. Under simultaneous recommendation the seller's expected revenue is the objective $R^M(\mathbf S,\mathbf P)$ of problem (13), where products of $\bar S\setminus S_i$ are bought from the store $l(i,k)$ that maximizes the customer's utility among the stores offering them. For each store $i$ let $\theta^*_i$ be the solution of
--   $$\theta^*_i=\sum_{k\in\mathcal N}e^{\hat\alpha_{ik}-\beta_{ik}\theta^*_i},\qquad \hat\alpha_{ik}=\alpha_{ik}-\log\beta_{ik}-1.$$
--
--   **Theorem 6.** The profile $\mathbf S^*=(\mathcal N,\dots,\mathcal N)$ with prices
--   $$p^*_{ik}=\theta^*_i+\frac{1}{\beta_{ik}}\qquad(i\in[m],\ k\in[n])$$
--   is an optimal solution of (13): for every assortment profile $\mathbf S$, every real price matrix $\mathbf P$ and every best-store rule $l$ for $(\mathbf S,\mathbf P)$,
--   $$R^M(\mathbf S,\mathbf P)\le R^M(\mathbf S^*,\mathbf P^*).$$
--
--   Under simultaneous recommendation, the joint assortment and pricing problem thus decouples: offering every product everywhere, at the single-store "constant adjusted markup" prices, earns as much as any coordinated multistore policy.
--
--   **Formalization Note** Optimality is a global upper bound over all profiles, all real prices and all tie-breaking rules $l$; uniqueness is not claimed. On the full profile $\bar S\setminus S_i=\emptyset$, so the right-hand side does not depend on its selection $l'$, which is quantified universally. $\theta^*_i$ enters as a hypothesis (the markup equation holds), whose solvability and uniqueness is a separate milestone. $\alpha_{ik}>0$ is the page's $\alpha_{ik}\in\mathbb R^+$; the statement remains true without it.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 28, Theorem 6; proof Online Supplement App. E.1, PDF p. 47

import Mathlib
import Definitions.Def_MultiStoreAssort_Pricing_Model

namespace MultiStoreAssort.Pricing
open Finset

theorem theorem6_full_assortment_markup {m n : ℕ} (lam : Fin m → ℝ) (α β : Fin m → Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1)
    (hα : ∀ i k, 0 < α i k) (hβ : ∀ i k, 0 < β i k) (hc : ∀ i j k, 0 ≤ c i j k)
    (hcii : ∀ i k, c i i k = 0) (θ : Fin m → ℝ) (hθ : ∀ i, IsTheta (α i) (β i) (θ i)) :
    ∀ (S : Fin m → Finset (Fin n)) (P : Fin m → Fin n → ℝ) (l l' : Fin m → Fin n → Fin m),
      IsBestStore α β c P S l →
        rev13 lam α β c S P l ≤
          rev13 lam α β c (fun _ => Finset.univ) (fun i k => θ i + 1 / β i k) l' := by sorry

end MultiStoreAssort.Pricing
