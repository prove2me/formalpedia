-- Prove2me | Theorems.Thm_NonlinFPE_Main_proposition_3_1
-- name    : NonlinFPE.Main.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:39.535879+00:00
-- url     : https://prove2.me/theorems/6ec0e8d3-bc62-4921-85d1-ec0cc3478978
-- title:
--   Proposition 3.1, pp. 9–10 — under (H1)–(H3), u + λAu = f has a unique solution in D(A) for every f ∈ L¹, λ > 0, with (3.11)–(3.13)
-- statement:
--   Assume (H1)–(H3). $L^1 = L^1(\mathbb R^d)$ is the Lebesgue space of (classes of) integrable real functions on $\mathbb R^d$, with norm $|u|_1 = \int |u|\,dx$. Let $A$ be the operator (3.8)–(3.9).
--
--   Then for each $f \in L^1$ and $\lambda > 0$ the equation
--   $$u - \lambda\sum_{i,j=1}^d D^2_{ij}\big(a_{ij}(x,u)u\big) + \lambda\operatorname{div}\big(b(x,u)u\big) = f \ \text{ in } \mathcal D'(\mathbb R^d), \tag{3.10}$$
--   i.e. $u + \lambda Au = f$, has a unique solution $u = u(\lambda,f) \in D(A)$. Moreover, for all $\lambda > 0$:
--
--   1. $|u(\lambda,f_1) - u(\lambda,f_2)|_1 \le |f_1 - f_2|_1$ for $f_1, f_2 \in L^1$; (3.11)
--   2. $(I+\lambda A)^{-1}f \ge 0$ a.e. if $f \ge 0$ a.e.; (3.12)
--   3. $\int_{\mathbb R^d}(I+\lambda A)^{-1}f\,dx = \int_{\mathbb R^d} f\,dx$. (3.13)
--
--   This is the resolvent theory behind the m-accretivity of $A$ in $L^1$ and the contraction, positivity and mass conservation of the semigroup.
--
--   **Formalization Note** Uniqueness is over all of $D(A)$, as printed. Properties (3.11)–(3.13) are stated for arbitrary solutions $u_k + \lambda v_k = f_k$, $v_k = Au_k$, so no resolvent is chosen.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, Proposition 3.1, pp. 9–10, (3.10)–(3.13)

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- Proposition 3.1, pp. 9–10, under (H1)–(H3): for every `f ∈ L¹` and `λ > 0` the equation
`u + λAu = f` ((3.10)) has a unique solution `u ∈ D(A)`; and for all `λ > 0` its solutions satisfy
the `L¹` contraction (3.11), positivity (3.12) and mass conservation (3.13). -/
theorem proposition_3_1 {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ) (γ : ℝ) (hND : HypND a b γ) :
    (∀ lam : ℝ, 0 < lam → ∀ f : SDEState d →₁[volume] ℝ,
      ∃! u : SDEState d →₁[volume] ℝ, ∃ v, opA a b u v ∧ u + lam • v = f) ∧
    (∀ lam : ℝ, 0 < lam → ∀ u₁ v₁ f₁ u₂ v₂ f₂ : SDEState d →₁[volume] ℝ,
      opA a b u₁ v₁ → u₁ + lam • v₁ = f₁ → opA a b u₂ v₂ → u₂ + lam • v₂ = f₂ →
        ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖) ∧
    (∀ lam : ℝ, 0 < lam → ∀ u v f : SDEState d →₁[volume] ℝ,
      opA a b u v → u + lam • v = f → 0 ≤ᵐ[volume] (f : SDEState d → ℝ) →
        0 ≤ᵐ[volume] (u : SDEState d → ℝ)) ∧
    (∀ lam : ℝ, 0 < lam → ∀ u v f : SDEState d →₁[volume] ℝ,
      opA a b u v → u + lam • v = f → ∫ x, u x = ∫ x, f x) := by sorry

end NonlinFPE.Main
