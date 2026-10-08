-- Prove2me | Theorems.Thm_MartOT_Product_eq_16
-- name    : MartOT.Product.eq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:12.963888+00:00
-- url     : https://prove2.me/theorems/29054b16-ffb5-4cb3-a4bc-dd9596e34f65
-- title:
--   Eq. (16), proof of Theorem 6.3, p. 38 — ∫ ϕ(x)ψ(y) dπ = ∫_0^∞ ∫ ψ dν^π_{ϕ^{-1}(t)} dt
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$, $\nu$ a Borel measure on $\mathbb R$ and $\pi$ a transport plan from $\mu$ to $\nu$. Let $\psi:\mathbb R\to[0,\infty)$ be Borel measurable and $\varphi:\mathbb R\to[0,\infty)$ nonincreasing. For $t>0$ let $\{\varphi\ge t\}=\{x\in\mathbb R:t\le\varphi(x)\}$, a left half-line, and let
--
--   $$\nu^\pi_{\{\varphi\ge t\}}=\mathrm{proj}^y_\#\big(\pi|_{\{\varphi\ge t\}\times\mathbb R}\big)$$
--
--   be the image under $\pi$ of the part of $\mu$ sitting on $\{\varphi\ge t\}$. Then, in $[0,\infty]$,
--
--   $$\int\varphi(x)\,\psi(y)\,d\pi(x,y)=\int_0^{+\infty}\Big(\int\psi(y)\,d\nu^\pi_{\{\varphi\ge t\}}(y)\Big)\,dt .$$
--
--   This layer-cake representation reduces the cost of a plan for the product cost $c(x,y)=\varphi(x)\psi(y)$ to a superposition of the costs $\int\psi\,d\nu^\pi_u$ of the left parts of $\mu$, which the left-curtain coupling minimizes one at a time.
--
--   **Formalization Note** The page writes the inner measure as $\nu^\pi_{\varphi^{-1}(t)}$ with $\varphi^{-1}(t)=\sup\{x:t\le\varphi(x)\}$, i.e. the restriction to $(-\infty,\varphi^{-1}(t)]$. For a nonincreasing $\varphi$ the superlevel set $\{\varphi\ge t\}$ is $(-\infty,\varphi^{-1}(t)]$ or $(-\infty,\varphi^{-1}(t))$; the two differ by one point, which matters when $\mu$ has an atom there, and only for $t$ in the jumps of $\varphi$. The statement uses the superlevel set, for which (16) holds exactly. The page's $\psi$ is strictly convex and $\varphi$ is decreasing; here only measurability of $\psi$ and monotonicity of $\varphi$ are assumed (a stronger statement). The integrals are lower Lebesgue integrals of nonnegative functions; for $c\ge0$ the left side is the cost $E_\pi[c]$ of the Setting layer.
-- source:
--   arXiv:1208.1509v2, §6, proof of Theorem 6.3, eq. (16), p. 38

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Product

open MeasureTheory

/-- **(16)** (proof of Theorem 6.3, p. 38), the layer-cake representation of the cost
`c(x, y) = ϕ(x)ψ(y)` of a plan `π` from `μ`: with `ν^π_{\{ϕ ≥ t\}} = proj^y_# π|_{\{ϕ ≥ t\}×ℝ}`,
`∫ ϕ(x)ψ(y) dπ = ∫_0^∞ ∫ ψ dν^π_{\{ϕ ≥ t\}} dt` in `[0, ∞]`. -/
theorem eq_16 (μ ν : Measure ℝ) [IsFiniteMeasure μ] (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsPlan μ ν π)
    (ψ ϕ : ℝ → ℝ) (hψ0 : ∀ y, 0 ≤ ψ y) (hψ : Measurable ψ) (hϕ0 : ∀ x, 0 ≤ ϕ x)
    (hϕ : Antitone ϕ) :
    ∫⁻ p, ENNReal.ofReal (ϕ p.1 * ψ p.2) ∂π =
      ∫⁻ t in Set.Ioi (0 : ℝ),
        ∫⁻ y, ENNReal.ofReal (ψ y) ∂((π.restrict ({x | t ≤ ϕ x} ×ˢ Set.univ)).map Prod.snd) := by sorry

end MartOT.Product
