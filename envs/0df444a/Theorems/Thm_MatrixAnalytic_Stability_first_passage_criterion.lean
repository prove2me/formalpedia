-- Prove2me | Theorems.Thm_MatrixAnalytic_Stability_first_passage_criterion
-- name    : MatrixAnalytic.Stability.first_passage_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:31.942824+00:00
-- url     : https://prove2.me/theorems/7e58131a-55cf-43b0-9328-f8bcdd220f6e
-- title:
--   Theorem 7.1.1 (first paragraphs) — recurrence and positive recurrence of a QBD from G, P^{0} = B + A₀G and m = M(1 + A₀G′(1)1)
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and a countable (finite or infinite) set of phases, and assume $P$ is stochastic and irreducible. Let $G$ be the first-passage matrix from $\ell(1)$ to $\ell(0)$ ($G_{ij}$ is the probability, starting from $(1, i)$, of ever reaching $\ell(0)$ and doing so first in $(0, j)$), let $P^{\{0\}} = B + A_0G$ be the transition matrix of the restricted chain on $\ell(0)$, let $G'(1)$ be given by (7.2), $M$ by (7.3)–(7.4) ($M_{ij}$ is the expected number of visits to $(0,j)$ from $(0,i)$ before the first return to $(0,i)$), and
--   $$\boldsymbol m = M(\mathbf 1 + A_0 G'(1)\mathbf 1).$$
--   Then:
--
--   1. if $G$ is substochastic ($G\mathbf 1 \le \mathbf 1$ with at least one strict inequality) or the chain $P^{\{0\}}$ is transient, the QBD is transient;
--   2. the QBD is recurrent if and only if $G$ is stochastic and the chain $P^{\{0\}}$ is recurrent;
--   3. the QBD is positive recurrent if and only if $G$ is stochastic, the chain $P^{\{0\}}$ is recurrent, and every component of $\boldsymbol m$ is finite.
--
--   This reduces the classification of the infinite chain to the matrix $G$ and a chain on a single level; the finite-phase case is the next item.
--
--   **Formalization Note** "The QBD is recurrent / positive recurrent / transient" means that every state is (`IsRecurrentChain` etc.); for an irreducible chain this is the same as for one state. Recurrence of $P^{\{0\}}$ uses the same return-time definition on the phases. $G$, $G'(1)$ and $M$ are defined probabilistically by trajectory sums with values in $[0,\infty]$, and "$\boldsymbol m$ is finite" is $m_i \ne \infty$ for every $i$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 149, Theorem 7.1.1 (first, second and third paragraphs)

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Definitions.Def_MatrixAnalytic_Stability_Passage

open scoped ENNReal

namespace MatrixAnalytic.Stability

/-- Theorem 7.1.1, first two paragraphs (p. 149), for any countable phase set. For an
irreducible QBD with first-passage matrix `G` (from `ℓ(1)` to `ℓ(0)`) and restricted chain
`P^{0} = B + A₀G` on `ℓ(0)`:
(1) if `G` is substochastic or `P^{0}` is transient, the QBD is transient;
(2) the QBD is recurrent iff `G` is stochastic and `P^{0}` is recurrent;
(3) the QBD is positive recurrent iff `G` is stochastic, `P^{0}` is recurrent and every
component of `m = M(1 + A₀G′(1)1)` is finite. -/
theorem first_passage_criterion {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ((IsSubstochasticE (matG (qbdP B A₀ A₁ A₂) 0) ∨
        IsTransientChain (restrictedP B A₀ (matG (qbdP B A₀ A₁ A₂) 0))) →
      IsTransientChain (qbdP B A₀ A₁ A₂)) ∧
    (IsRecurrentChain (qbdP B A₀ A₁ A₂) ↔
      IsStochasticE (matG (qbdP B A₀ A₁ A₂) 0) ∧
        IsRecurrentChain (restrictedP B A₀ (matG (qbdP B A₀ A₁ A₂) 0))) ∧
    (IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂) ↔
      IsStochasticE (matG (qbdP B A₀ A₁ A₂) 0) ∧
        IsRecurrentChain (restrictedP B A₀ (matG (qbdP B A₀ A₁ A₂) 0)) ∧
        ∀ i : ι, vecm (qbdP B A₀ A₁ A₂) A₀ i ≠ ⊤) := by sorry

end MatrixAnalytic.Stability
