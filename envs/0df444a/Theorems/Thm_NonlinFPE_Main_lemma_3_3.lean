-- Prove2me | Theorems.Thm_NonlinFPE_Main_lemma_3_3
-- name    : NonlinFPE.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:44.382522+00:00
-- url     : https://prove2.me/theorems/93381fb1-0899-4297-97e1-c8a427766a28
-- title:
--   Lemma 3.3, p. 12 — under (H1)–(H3) and (K), for λ < λ₀ equation (3.10) has a solution u ∈ H¹(ℝ^d) with |u|₂² + γλ|∇u|₂² ≤ C(|f|₂² + 1)
-- statement:
--   Assume (H1)–(H3) with ellipticity constant $\gamma > 0$ and the additional hypotheses (K), (3.15).
--
--   There are $\lambda_0 > 0$ and a constant $C$ such that for every $\lambda \in (0,\lambda_0)$ and every $f \in L^2(\mathbb R^d)$ the equation
--   $$u - \lambda\sum_{i,j=1}^d D^2_{ij}\big(a_{ij}(x,u)u\big) + \lambda\operatorname{div}\big(b(x,u)u\big) = f \ \text{ in } \mathcal D'(\mathbb R^d) \tag{3.10}$$
--   has at least one solution $u \in H^1(\mathbb R^d)$ satisfying
--   $$|u|_2^2 + \gamma\lambda|\nabla u|_2^2 \le C\big(|f|_2^2 + 1\big). \tag{3.20}$$
--
--   Together with the uniqueness and $L^1$-contraction (3.22) this gives the resolvent of $A$ on $L^2 \cap L^1$ data under (K).
--
--   **Formalization Note** As in Lemma 3.2, *some* $\lambda_0 > 0$ replaces the printed $\lambda_0 = \gamma(b_\infty^2+c_\infty^2)^{-1}$ (disclosed weakening), and $0 < \lambda$ is made explicit. $C$ is quantified before $\lambda$ and $f$, so it is one constant for all data. $H^1$ is encoded by an explicit weak gradient $g$ with $|\nabla u|_2^2 = \int\sum_i g_i^2$; the equation is the derivative-free weak form in $\mathcal D'(\mathbb R^d)$.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, Lemma 3.3, p. 12, (3.10), (3.20); hypotheses (K), (3.15), p. 10

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- Lemma 3.3, p. 12, under (H1)–(H3) and (K): for some `λ₀ > 0` and some `C`, for every
`λ ∈ (0, λ₀)` and `f ∈ L²(ℝᵈ)` equation (3.10) has a solution `u ∈ H¹(ℝᵈ)` with
`|u|₂² + γλ|∇u|₂² ≤ C(|f|₂² + 1)`. -/
theorem lemma_3_3 {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ) (γ : ℝ) (hND : HypND a b γ) (hK : HypK a b) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∃ C : ℝ,
      ∀ lam : ℝ, 0 < lam → lam < lam0 → ∀ f : SDEState d → ℝ, MemLp f 2 volume →
        ∃ (u : SDEState d → ℝ) (g : Fin d → SDEState d → ℝ),
          IsH1 u g ∧ ResolventEqOn Set.univ a b lam u f ∧
          (∫ x, u x ^ 2) + γ * lam * ∫ x, ∑ i, g i x ^ 2 ≤ C * ((∫ x, f x ^ 2) + 1) := by sorry

end NonlinFPE.Main
