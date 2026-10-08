-- Prove2me | Theorems.Thm_NonlinFPE_Main_eq_3_22
-- name    : NonlinFPE.Main.eq_3_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:54.524975+00:00
-- url     : https://prove2.me/theorems/580c9d75-2814-4c18-b450-3c6a27d40883
-- title:
--   (3.22), proof of Proposition 3.1, pp. 13, 16 — under (H1)–(H3), (K) and λ ∈ (0, λ₀), H¹ solutions of (3.10) satisfy |u₁ − u₂|₁ ≤ |f₁ − f₂|₁
-- statement:
--   Assume (H1)–(H3) with ellipticity constant $\gamma > 0$ and (K), (3.15). Let
--   $$\lambda_0 = \gamma\,(b_\infty^2 + c_\infty^2)^{-1}, \qquad b_\infty = \sup|b_i(x,u)|, \quad c_\infty = \sup|(a_{ij})_{x_j}(x,u)|,$$
--   and $0 < \lambda < \lambda_0$. If $u_1, u_2 \in H^1(\mathbb R^d)$ solve (3.10) with right-hand sides $f_1, f_2 \in L^2 \cap L^1$ respectively, then
--   $$|u_1 - u_2|_1 \le |f_1 - f_2|_1. \tag{3.22}$$
--   In particular the $H^1$ solution of (3.10) is unique for such $f$ and $\lambda$.
--
--   This $L^1$-contraction is what survives the passage to general $L^1$ data and gives (3.11) and the accretivity of $A$.
--
--   **Formalization Note** The condition $\lambda < \lambda_0$ is written $\lambda(b_\infty^2 + c_\infty^2) < \gamma$, which is the page's condition when $b_\infty^2 + c_\infty^2 > 0$ and reads $\lambda_0 = +\infty$ when it vanishes (a literal $\gamma/0$ would be $0$ in Lean and empty the statement). Since $u_i$ are only assumed in $H^1$, the norms are lower Lebesgue integrals in $[0,\infty]$, so the inequality also asserts $u_1 - u_2 \in L^1$.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, §3.1, proof of Proposition 3.1, p. 13, (3.22), and summary p. 16; b∞, c∞, λ₀, p. 11; (K), p. 10

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- (3.22), proof of Proposition 3.1, p. 13 (summary p. 16), under (H1)–(H3) and (K): for
`0 < λ < λ₀ = γ(b∞² + c∞²)⁻¹` (written `λ(b∞² + c∞²) < γ`, so that `λ₀ = ∞` when
`b∞ = c∞ = 0`), any two `H¹` solutions `u₁, u₂` of (3.10) with data `f₁, f₂ ∈ L² ∩ L¹` satisfy
`|u₁ - u₂|₁ ≤ |f₁ - f₂|₁` (in `[0, ∞]`); in particular the `H¹` solution is unique. -/
theorem eq_3_22 {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ) (γ : ℝ) (hND : HypND a b γ) (hK : HypK a b)
    (lam : ℝ) (hlam : 0 < lam) (hlam0 : lam * (bSup b ^ 2 + cSup a ^ 2) < γ)
    (f₁ f₂ u₁ u₂ : SDEState d → ℝ) (g₁ g₂ : Fin d → SDEState d → ℝ)
    (hf₁ : MemLp f₁ 2 volume) (hf₁' : Integrable f₁ volume)
    (hf₂ : MemLp f₂ 2 volume) (hf₂' : Integrable f₂ volume)
    (hu₁ : IsH1 u₁ g₁) (hu₂ : IsH1 u₂ g₂)
    (he₁ : ResolventEqOn Set.univ a b lam u₁ f₁) (he₂ : ResolventEqOn Set.univ a b lam u₂ f₂) :
    ∫⁻ x, ‖u₁ x - u₂ x‖ₑ ≤ ∫⁻ x, ‖f₁ x - f₂ x‖ₑ := by sorry

end NonlinFPE.Main
