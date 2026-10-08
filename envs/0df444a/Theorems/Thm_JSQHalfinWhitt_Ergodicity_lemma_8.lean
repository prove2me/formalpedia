-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Ergodicity_lemma_8
-- name    : JSQHalfinWhitt.Ergodicity.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:29.454035+00:00
-- url     : https://prove2.me/theorems/e89af431-c767-438a-bfad-2e1999b91f2f
-- title:
--   Lemma 8 — with κ₁ = β + ϵ, κ₂ = β + 2ϵ the PDEs (5.9)–(5.10) have C²(Ω) solutions with the bounds (5.13)–(5.16)
-- statement:
--   Fix an integer $n\ge1$, $\beta>0$ and $\epsilon>0$, set $\kappa_1=\beta+\epsilon$, $\kappa_2=\beta+2\epsilon$, and let $\phi=\phi^{(\kappa_1/\sqrt n,\kappa_2/\sqrt n)}$ be the smoothed indicator (5.5). Then there are functions $f^{(1)},f^{(2)}\in C^2(\Omega)$ solving the PDEs
--   $$Lf^{(1)}(x)=-\phi(-x_1),\quad x\in\Omega,\qquad f^{(1)}_1(0,x_2)=f^{(1)}_2(0,x_2),\quad x_2\ge0,\qquad(5.9)$$
--   $$Lf^{(2)}(x)=-\phi(x_2),\quad x\in\Omega,\qquad f^{(2)}_1(0,x_2)=f^{(2)}_2(0,x_2),\quad x_2\ge0,\qquad(5.10)$$
--   where $Lf=(-x_1+x_2-\beta/\sqrt n)f_1-x_2f_2$, such that
--
--   1. (5.13) $f^{(1)}(x)\le\log2$ and (5.14) $f^{(2)}(x)\le\log2+\epsilon/\beta$ for $x\in[-\kappa_2/\sqrt n,0]\times[0,\kappa_2/\sqrt n]$;
--   2. (5.15)–(5.16) for all $x\in\Omega$,
--   $$|f^{(1)}_1(x)|\le\frac{4\sqrt n}{\epsilon}\log2,\quad |f^{(1)}_{11}(x)|\le\frac{12n}{\epsilon^2}\log2,\quad |f^{(2)}_1(x)|\le\frac{\sqrt n}{\beta},\quad |f^{(2)}_{11}(x)|\le\frac{n}{\beta\epsilon}\Big(1+4\frac{\beta+\epsilon}{\epsilon}\Big).$$
--
--   These are the facts the proof of Theorem 4 uses: the PDEs make the leading term of $G_YV$ negative outside a box, and the bounds make the remaining terms small and independent of $n$ once $\epsilon$ is large and $\alpha$ small.
--
--   **Formalization Note** The printed Lemma 8 fixes $\kappa_1<\kappa_2$ with $\kappa_1>\beta$ and then asserts the bounds "for every $\epsilon>0$". Read literally, (5.15) with $\epsilon\to\infty$ forces $f^{(1)}_1\equiv0$, which contradicts (5.9) at points $(x_1,0)$ with $x_1\le-\kappa_2/\sqrt n$, where $\phi(-x_1)=1$. The proof ties $\epsilon$ to the levels: "Choosing $\kappa_1=\beta+\epsilon$ and $\kappa_2=\beta+2\epsilon$ proves (5.15) … proves (5.13)" (p. 38), and the bounds on p. 44 give (5.14) and (5.16) with the same choice. The statement formalized is this corrected one: for every $\epsilon>0$, with $\kappa_1=\beta+\epsilon$, $\kappa_2=\beta+2\epsilon$. Partials are one-sided partials on $\Omega$, and $C^2(\Omega)$ is `ContDiffOn ℝ 2 · Ω`. No relation between $\beta$ and $\sqrt n$ is assumed: $n$ only rescales the auxiliary functions.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), pp. 18–19, Lemma 8, (5.9)–(5.10), (5.13)–(5.16); choice κ_1 = β + ϵ, κ_2 = β + 2ϵ on p. 38 and the bounds on p. 44

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Ergodicity_Operators

namespace JSQHalfinWhitt.Ergodicity

/-- Lemma 8, pp. 18–19, in the form its proof establishes (p. 38, p. 44): let `n ≥ 1`, `β > 0`,
`ϵ > 0`, `κ₁ = β + ϵ`, `κ₂ = β + 2ϵ` and `φ = φ^{(κ₁/√n, κ₂/√n)}`. Then there are
`f^{(1)}, f^{(2)} ∈ C²(Ω)` solving the PDEs (5.9)–(5.10),
`Lf^{(1)}(x) = −φ(−x₁)`, `Lf^{(2)}(x) = −φ(x₂)` on `Ω`, `f^{(i)}₁(0, x₂) = f^{(i)}₂(0, x₂)` for `x₂ ≥ 0`,
with (5.13) `f^{(1)} ≤ log 2` and (5.14) `f^{(2)} ≤ log 2 + ϵ/β` on `[−κ₂/√n, 0] × [0, κ₂/√n]`, and on
all of `Ω` (5.15) `|f^{(1)}₁| ≤ (4√n/ϵ) log 2`, `|f^{(1)}₁₁| ≤ (12n/ϵ²) log 2` and (5.16)
`|f^{(2)}₁| ≤ √n/β`, `|f^{(2)}₁₁| ≤ (n/(βϵ))(1 + 4(β + ϵ)/ϵ)`. -/
theorem lemma_8 (n : ℕ) (hn : 0 < n) (β ε κ1 κ2 : ℝ) (hβ : 0 < β) (hε : 0 < ε)
    (hκ1 : κ1 = β + ε) (hκ2 : κ2 = β + 2 * ε) :
    ∃ f1 f2 : ℝ × ℝ → ℝ,
      ContDiffOn ℝ 2 f1 JSQHalfinWhitt.Tightness.Omega ∧ ContDiffOn ℝ 2 f2 JSQHalfinWhitt.Tightness.Omega ∧
      -- (5.9)
      (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, opL n β f1 x =
        -smoothInd (κ1 / Real.sqrt n) (κ2 / Real.sqrt n) (-x.1)) ∧
      (∀ x2 : ℝ, 0 ≤ x2 → d1 f1 (0, x2) = d2 f1 (0, x2)) ∧
      -- (5.10)
      (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, opL n β f2 x =
        -smoothInd (κ1 / Real.sqrt n) (κ2 / Real.sqrt n) x.2) ∧
      (∀ x2 : ℝ, 0 ≤ x2 → d1 f2 (0, x2) = d2 f2 (0, x2)) ∧
      -- (5.13), (5.14)
      (∀ x : ℝ × ℝ, -κ2 / Real.sqrt n ≤ x.1 → x.1 ≤ 0 → 0 ≤ x.2 → x.2 ≤ κ2 / Real.sqrt n →
        f1 x ≤ Real.log 2) ∧
      (∀ x : ℝ × ℝ, -κ2 / Real.sqrt n ≤ x.1 → x.1 ≤ 0 → 0 ≤ x.2 → x.2 ≤ κ2 / Real.sqrt n →
        f2 x ≤ Real.log 2 + ε / β) ∧
      -- (5.15)
      (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, |d1 f1 x| ≤ 4 * Real.sqrt n / ε * Real.log 2 ∧
        |d11 f1 x| ≤ 12 * n / ε ^ 2 * Real.log 2) ∧
      -- (5.16)
      (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, |d1 f2 x| ≤ Real.sqrt n / β ∧
        |d11 f2 x| ≤ n / (β * ε) * (1 + 4 * ((β + ε) / ε))) := by sorry

end JSQHalfinWhitt.Ergodicity
