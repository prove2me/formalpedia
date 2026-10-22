-- Prove2me | Theorems.Thm_NCLpModules_Principal_lemma_1_4
-- name    : NCLpModules.Principal.lemma_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:02.195541+00:00
-- url     : https://prove2.me/theorems/6e28eb34-a9c0-45f8-ae75-e7a668f2677c
-- title:
--   Lemma 1.4, p. 4 — a bounded compatible net ξ_α = ξ_α p_α, ξ_β p_α = ξ_α (α < β) in L^r, r < ∞, converges in norm to ξ with ξ_β = ξ p_β
-- statement:
--   Let $\mathcal M\subseteq M_n(\mathbb C)$ be a unital $*$-subalgebra and $0<r<\infty$. Let $(I,\le)$ be a nonempty directed partially ordered set, $(\xi_\alpha)_{\alpha\in I}$ a net in $L^r(\mathcal M)=\mathcal M$ and $(p_\alpha)_{\alpha\in I}$ a net of projections of $\mathcal M$ such that
--   $$\xi_\alpha=\xi_\alpha p_\alpha,\qquad \xi_\beta p_\alpha=\xi_\alpha\ \text{ for }\alpha<\beta,\qquad \|\xi_\alpha\|_r\le C\ \text{ for all }\alpha. \tag{1.3}$$
--   Then $\xi_\alpha$ converges in $\|\cdot\|_r$ to some $\xi\in L^r(\mathcal M)$, and $\xi_\beta=\xi\,p_\beta$ for every $\beta$.
--
--   Adding columns (enlarging the right support) under a uniform $L^r$ bound forces convergence; in the paper this is used to build elements of $L^p$ modules as limits in Case 3 of the proof of Theorem 2.5.
--
--   **Formalization Note** Finite-dimensional scope; $\|\cdot\|_r$ is the tracial Schatten (quasi)norm `lpNorm r`. The page's $\sup_\alpha\|\xi_\alpha\|=C<\infty$ is encoded as the bound $\|\xi_\alpha\|_r\le C$ for all $\alpha$ ($C$ appears in no conclusion). The index set is a partial order (for a preorder with distinct equivalent indices the statement fails, since no relation $\alpha<\beta$ links them). Convergence is `Tendsto (fun α => ‖ξ_α − ξ‖_r) atTop (𝓝 0)`. The projections need not increase.
-- source:
--   Junge & Sherman, Noncommutative Lp modules, arXiv:math/0301044v2, p. 4, Lemma 1.4 and (1.3)

import Mathlib
import Definitions.Def_NCLpModules_Principal_Model

namespace NCLpModules.Principal

open scoped Matrix ComplexOrder

open Filter
open scoped Topology

theorem lemma_1_4 {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    {r : ℝ} (hr : 0 < r)
    {I : Type*} [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (ξ P : I → Matrix (Fin n) (Fin n) ℂ) (hξM : ∀ α, ξ α ∈ M) (hP : ∀ α, IsProj M (P α))
    (h₁ : ∀ α, ξ α = ξ α * P α) (h₂ : ∀ α β, α < β → ξ β * P α = ξ α)
    (C : ℝ) (hC : ∀ α, lpNorm r (ξ α) ≤ C) :
    ∃ ξ' ∈ M, Tendsto (fun α => lpNorm r (ξ α - ξ')) atTop (𝓝 0) ∧
      ∀ β, ξ β = ξ' * P β := by sorry

end NCLpModules.Principal
