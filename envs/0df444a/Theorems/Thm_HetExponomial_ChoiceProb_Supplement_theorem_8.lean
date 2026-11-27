-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_8
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:39:52.875332+00:00
-- url     : https://prove2.me/theorems/e20e92ee-4f01-4030-a952-82d1f01461f1
-- title:
--   Theorem 8, pp. 25–26 — every optimal monopoly price vector: p*, u* nondecreasing in α; hockey stick with the elbow at u_l = α_l
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. In the pricing model, product $i$ has ideal utility $u_i=\alpha_i-\beta p_i$ at price $p_i$, with intrinsic desirability $\alpha_i\in\mathbb R$ and price sensitivity $\beta>0$; market size is $1$ and marginal costs are $0$. Consider the monopoly of Theorem 7 with outside option $l$, and let $\mathbf p^*$ be **any** optimal price vector, with $u^*_i=\alpha_i-\beta p^*_i$. Then
--
--   1. for all products $i,j\ne l$, $\alpha_i\le\alpha_j$ implies $p^*_i\le p^*_j$ and $u^*_i\le u^*_j$;
--   2. if the products' intrinsic desirabilities are distinct (so that the products can be indexed with $\alpha_i$ increasing in $i$), the prices form a **hockey stick**: the products split into those before the outside option and those after it in increasing $\alpha$-order, with
--   $$
--   p^*_1=\dots=p^*_{l-1}<p^*_{l+1}<\dots<p^*_n,\qquad u^*_1\le\dots\le u^*_{l-1}\le u_l=\alpha_l\le u^*_{l+1}\le\dots\le u^*_n .
--   $$
--   Concretely: there is a set $B$ of products (not containing $l$) such that every product in $B$ has smaller $\alpha$ than every product outside $B\cup\{l\}$; $u^*_i\le\alpha_l$ on $B$ and $u^*_j\ge\alpha_l$ off $B$; all prices on $B$ are equal; off $B$, $\alpha_i<\alpha_j$ implies $p^*_i<p^*_j$; and every price on $B$ is strictly below every price off $B$.
--
--   **Formalization Note** The statement holds for every maximizer of $R$ over real price vectors with $p_l=0$. Part 1 also gives the two $u^*$ chains.
--
--   Differences from the source:
--   - reading: "indexing the products such that α_i is increasing in i" → the hockey-stick clause assumes the α_i of the products other than l are pairwise distinct; reason: "increasing" read as strictly increasing; the theorem says "nondecreasing" for the weak sense, and with tied α a strict price chain would contradict part 1 for tied products
--   - encoding: indices 1, …, l−1 before and l+1, …, n after the outside option → a Finset B of products before the outside option, every one with smaller α than every product after it; reason: the paper's relabeling places l by the crossing of u* and u_l; B is that initial segment
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), pp. 25–26, Theorem 8; proof pp. 52–57

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_8 {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (l : Fin n) (p : Fin n → ℝ)
    (hp : IsOptimalMonopolyPrice α β lam l p) :
    (∀ i j, i ≠ l → j ≠ l → α i ≤ α j → p i ≤ p j ∧ util α β p i ≤ util α β p j) ∧
      ((∀ i j, i ≠ l → j ≠ l → i ≠ j → α i ≠ α j) →
        ∃ B : Finset (Fin n), l ∉ B ∧
          (∀ i ∈ B, ∀ j, j ≠ l → j ∉ B → α i < α j) ∧
          (∀ i ∈ B, util α β p i ≤ α l) ∧
          (∀ j, j ≠ l → j ∉ B → α l ≤ util α β p j) ∧
          (∀ i ∈ B, ∀ j ∈ B, p i = p j) ∧
          (∀ i j, i ≠ l → j ≠ l → i ∉ B → j ∉ B → α i < α j → p i < p j) ∧
          (∀ i ∈ B, ∀ j, j ≠ l → j ∉ B → p i < p j)) := by sorry

end HetExponomial.ChoiceProb.Supplement
