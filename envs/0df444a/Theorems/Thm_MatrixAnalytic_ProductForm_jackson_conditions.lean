-- Prove2me | Theorems.Thm_MatrixAnalytic_ProductForm_jackson_conditions
-- name    : MatrixAnalytic.ProductForm.jackson_conditions
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:27.22277+00:00
-- url     : https://prove2.me/theorems/095fb960-6585-4e1b-86b4-57bca1689456
-- title:
--   Theorem 15.2.1 — the Jackson network satisfies the conditions of Theorem 15.1.3 with η = y₁/μ₁ and θ of product form
-- statement:
--   Consider the Jackson network with $K$ nodes, service rates $\mu_i>0$, external arrival rates $\lambda_i\ge 0$, routing matrix $P$ with $P_{ij}\ge 0$ and $P_{ii}=0$, and exit probabilities $q_i\ge 0$ with $\sum_jP_{ij}+q_i=1$, the network being open ($I-P$ invertible). Write it as a QBD with level $n_1$ and phase $\boldsymbol r=(n_2,\dots,n_K)$, blocks $A_0,A_1,A_2$ and $B=A_1+\mu_1I$ as in the file `Jackson`, and assume this QBD irreducible. Let $\boldsymbol y$ be the solution of the traffic equations
--   $$\boldsymbol y=\boldsymbol\lambda+\boldsymbol yP, \tag{15.14}$$
--   where $\boldsymbol\lambda=(\lambda_1,\dots,\lambda_K)$. If $y_i/\mu_i<1$ for all $i$, then the conditions of Theorem 15.1.3 are satisfied by the scalar
--   $$\eta=y_1/\mu_1 \tag{15.15}$$
--   and the vector $\boldsymbol\theta$ with
--   $$\theta_{\boldsymbol r}=c\prod_{2\le j\le K}(y_j/\mu_j)^{n_j},\qquad c=\prod_{2\le j\le K}(1-y_j/\mu_j): \tag{15.16}$$
--   $\boldsymbol\theta$ is positive, $\boldsymbol\theta\mathbf 1=1$, $0<\eta<1$, $\boldsymbol\theta(A_0+\eta A_1+\eta^2A_2)=\mathbf 0$ and $\boldsymbol\theta(B+\eta A_2)=\mathbf 0$.
--
--   Combined with Theorem 15.1.3 this recovers the product form of the Jackson network: the number of customers at node 1 is geometric and independent of the rest of the network, whose distribution factors over nodes $2,\dots,K$.
--
--   **Formalization Note** Nodes are `Option J` with `J` finite: `none` is node $1$, `some j` are nodes $2,\dots,K$; $\lambda$ is written `lam` and $P$ is a matrix over `Option J`. The book's "the solution of the traffic equations" presupposes that it is unique; this is carried as the hypothesis that $I-P$ is invertible (the network is open), and $\boldsymbol y$ is any vector with $\boldsymbol y=\boldsymbol\lambda+\boldsymbol yP$. Irreducibility of the QBD is the chapter's standing assumption; it is what makes every $y_i$ positive, so that $\boldsymbol\theta$ and $\eta$ are positive. Regularity, the other standing assumption, is not needed for these algebraic conditions and is omitted. The two conditions are convergent sums over the countable phase set $\mathbb N^{K-1}$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 300–301, Theorem 15.2.1

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_MatrixAnalytic_ProductForm_QBD
import Definitions.Def_MatrixAnalytic_ProductForm_Jackson

namespace MatrixAnalytic.ProductForm

/-- Theorem 15.2.1 (pp. 300–301). For the Jackson network of §15.2 written as a QBD (level
`n₁`, phase `r = (n₂, …, n_K)`, blocks (15.7)ff., `B = A₁ + μ₁I`), irreducible, with routing
matrix `P` (`P_ii = 0`, the network open) and `y` the solution of the traffic equations
`y = λ + yP` (15.14): if `y_i/μ_i < 1` for every node `i`, then `η = y₁/μ₁` (15.15) and
`θ_r = c ∏_{2 ≤ j ≤ K} (y_j/μ_j)^{n_j}` (15.16), `c = ∏_{2 ≤ j ≤ K} (1 − y_j/μ_j)`, satisfy the
conditions of Theorem 15.1.3: `θ > 0`, `θ1 = 1`, `0 < η < 1`, `θ(A₀ + ηA₁ + η²A₂) = 0` and
`θ(B + ηA₂) = 0`. Node `1` is `none`, nodes `2, …, K` are `some j`, `j : J`. -/
theorem jackson_conditions {J : Type*} [Fintype J] [DecidableEq J]
    (lam μ q y : Option J → ℝ) (P : Matrix (Option J) (Option J) ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hμ : ∀ i, 0 < μ i)
    (hP : ∀ i j, 0 ≤ P i j) (hPii : ∀ i, P i i = 0)
    (hq : ∀ i, 0 ≤ q i) (hrow : ∀ i, ∑ j, P i j + q i = 1)
    (hopen : IsUnit (1 - P))
    (hirr : IrreducibleCT (qbdQ (jacksonB lam μ q P) (jacksonA₀ lam μ P)
      (jacksonA₁ lam μ q P) (jacksonA₂ μ q P)))
    (htraffic : y = lam + Matrix.vecMul y P)
    (hload : ∀ i, y i / μ i < 1) :
    let η : ℝ := y none / μ none
    let c : ℝ := ∏ j : J, (1 - y (some j) / μ (some j))
    let θ : (J → ℕ) → ℝ := fun r => c * ∏ j : J, (y (some j) / μ (some j)) ^ r j
    (∀ r, 0 < θ r) ∧ HasSum θ 1 ∧ 0 < η ∧ η < 1 ∧
      (∀ s, HasSum (fun r => θ r * (jacksonA₀ lam μ P r s + η * jacksonA₁ lam μ q P r s +
        η ^ 2 * jacksonA₂ μ q P r s)) 0) ∧
      (∀ s, HasSum (fun r => θ r * (jacksonB lam μ q P r s + η * jacksonA₂ μ q P r s)) 0) := by sorry

end MatrixAnalytic.ProductForm
