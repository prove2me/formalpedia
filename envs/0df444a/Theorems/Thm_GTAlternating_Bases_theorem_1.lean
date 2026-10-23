-- Prove2me | Theorems.Thm_GTAlternating_Bases_theorem_1
-- name    : GTAlternating.Bases.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:08.545364+00:00
-- url     : https://prove2.me/theorems/2e8e94a6-d2c0-4958-be23-5c8920d9b2d0
-- title:
--   Theorem 1 (1)–(2), p. 9 — V_λ|A_n ≅ V_λ′|A_n irreducible for λ ≠ λ′; V_λ^+ and V_λ^- non-isomorphic irreducibles for λ = λ′
-- statement:
--   Let $n \ge 2$ and let $\lambda$ be a partition of $n$.
--
--   1. If $\lambda \ne \lambda'$, then the restrictions of $V_\lambda$ and $V_{\lambda'}$ to $A_n$ are irreducible, and there is an $A_n$-equivariant linear isomorphism $V_\lambda \to V_{\lambda'}$.
--   2. If $\lambda = \lambda'$, then $V_\lambda^{+}$ and $V_\lambda^{-}$ are irreducible representations of $A_n$, and there is no $A_n$-equivariant linear map $V_\lambda \to V_\lambda$ restricting to an isomorphism $V_\lambda^{+} \xrightarrow{\sim} V_\lambda^{-}$.
--
--   These are the irreducible representations $V_\alpha$, $\alpha \in \tilde\Theta(n)$, that the Gelfand–Tsetlin bases of the paper live in.
--
--   **Formalization Note.** Irreducibility is stated as: the subspace is nonzero, stable under all $\rho(s_i)\rho(s_j)$ with $i,j \le n-1$, and contains no other stable subspace except $0$. An isomorphism $V_\lambda^+ \cong V_\lambda^-$ of $A_n$-representations is the same as an $A_n$-equivariant map on $V_\lambda$ that restricts to a bijection $V_\lambda^+ \to V_\lambda^-$ (extend by zero on $V_\lambda^-$). $A_n$-equivariance is commutation with the generators $s_is_j$. The final sentence of Theorem 1 (that these exhaust the irreducibles of $A_n$) is not stated: this model has no group $A_n$ whose irreducibles could be enumerated.
-- source:
--   Geetha, Prasad, Comparison of Gelfand-Tsetlin bases for alternating and symmetric groups, arXiv:1606.04424v2, p. 9, Theorem 1 (1)–(2)

import Mathlib
import Definitions.Def_GTAlternating_Bases_Model

namespace GTAlternating.Bases

theorem theorem_1 (n : ℕ) (hn : 2 ≤ n) (lam : YoungDiagram) (hlam : lam.cells.card = n) :
    (lam.transpose ≠ lam →
      IsAltIrreducible n (⊤ : Submodule ℂ (V lam)) ∧
      IsAltIrreducible n (⊤ : Submodule ℂ (V lam.transpose)) ∧
      ∃ f : V lam →ₗ[ℂ] V lam.transpose, IsAltEquivariant n f ∧ Function.Bijective f) ∧
    (lam.transpose = lam →
      IsAltIrreducible n (Vpm lam true) ∧ IsAltIrreducible n (Vpm lam false) ∧
      ¬ ∃ f : V lam →ₗ[ℂ] V lam, IsAltEquivariant n f ∧ Set.InjOn f (Vpm lam true) ∧
        (Vpm lam true).map f = Vpm lam false) := by sorry

end GTAlternating.Bases
