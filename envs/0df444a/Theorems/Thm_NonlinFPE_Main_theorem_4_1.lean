-- Prove2me | Theorems.Thm_NonlinFPE_Main_theorem_4_1
-- name    : NonlinFPE.Main.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:54.363374+00:00
-- url     : https://prove2.me/theorems/7a319952-a881-4dc9-8e04-bd5a7880edca
-- title:
--   Theorem 4.1, p. 24 — under (H1)–(H3) or (H1)′–(H3)′ the McKean–Vlasov SDE (4.1) has a weak solution with P∘X(t)⁻¹ = u(t,x)dx
-- statement:
--   Let $\sigma : \mathbb R^d\times\mathbb R \to L(\mathbb R^d;\mathbb R^d)$ and $b : \mathbb R^d\times\mathbb R \to \mathbb R^d$ be measurable, put $a_{ij} = (\sigma\sigma^T)_{ij}$, and assume that $a$, $b$ satisfy either (H1)–(H3) or (H1)′–(H3)′. Let $u_0$ be a probability density on $\mathbb R^d$. Consider, for $T \in (0,\infty)$, the McKean–Vlasov SDE
--   $$dX(t) = b\Big(X(t), \frac{d\mathcal L_{X(t)}}{dx}(X(t))\Big)dt + \sqrt2\,\sigma\Big(X(t), \frac{d\mathcal L_{X(t)}}{dx}(X(t))\Big)dW(t), \quad 0 \le t \le T, \qquad X(0) = \xi_0, \tag{4.1}$$
--   with $P\circ\xi_0^{-1}(dx) = u_0(x)dx$, where $\mathcal L_{X(t)}$ is the law of $X(t)$.
--
--   Then the nonlinear FPE (3.1) (resp. (3.41)) has a weak solution $u$ with $u(0) = u_0$ (Theorems 3.4 and 3.7), and for this $u$ and every $T > 0$ there is a (probabilistically) weak solution $X$ of (4.1) on some filtered probability space with a Brownian motion $W$, such that
--   $$u(t,x)\,dx = P\circ X(t)^{-1}(dx), \qquad 0 \le t \le T .$$
--   In (4.1) the density $\frac{d\mathcal L_{X(t)}}{dx}$ is thus $u(t,\cdot)$.
--
--   This is the paper's main result: weak existence for a McKean–Vlasov SDE whose coefficients depend on the density of the solution's own law, pointwise at the current position, obtained from the nonlinear FPE.
--
--   **Formalization Note** The page prints $a_{ij} := 2(\sigma\sigma^T)_{ij}$; this is a misprint. By Itô's formula the noise $\sqrt2\sigma$ has generator $\sum_{i,j}(\sigma\sigma^T)_{ij}\partial_{ij} + b\cdot\nabla$, so the marginals of (4.1) solve (3.1) exactly for $a = \sigma\sigma^T$. With the printed factor the statement is false ($d = 1$, $\sigma \equiv 1/\sqrt2$, $b \equiv 0$: (3.1) is $\partial_tu = \partial_{xx}u$, variance $2t$, while $X = W$ has variance $t$). "The solution $u$" is any mild solution for the operator $A$ of (3.8)–(3.9) with these coefficients (it is unique); its existence is the first conjunct. The SDE's coefficients are evaluated on a jointly measurable version $\tilde u(t,x)$ of $u$ that agrees a.e. with $u(t)$ for $t \le T$ and is the density of $X(t)$; the weak solution is the published `EthierKurtz.IsWeakSDESolution` on $[0,\infty)$ with coefficients switched off after $T$, so the representation is asserted on $[0,T]$ (the page's "$t \ge 0$" with (4.1) posed on $[0,T]$). In the degenerate case the hypothesis says $a = \sigma\sigma^T$ and $b$ do not depend on $x$.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, Theorem 4.1, p. 24, and (4.1), p. 23; Theorems 3.4 (p. 18) and 3.7 (p. 22)

import Mathlib
import Definitions.Def_EthierKurtz_IsWeakSDESolution
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive
import Definitions.Def_NonlinFPE_Main_SDE

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- Theorem 4.1, p. 24 (with (4.1), p. 23), drafted with `aᵢⱼ = (σσᵀ)ᵢⱼ` (the page prints
`2(σσᵀ)ᵢⱼ`, a misprint for the noise `√2 σ`). Let `σ`, `b` be measurable with `a = σσᵀ`, `b`
satisfying (H1)–(H3) or (H1)′–(H3)′, and `u₀` a probability density. Then (3.2) for the operator
`A` of (3.8)–(3.9) has a mild solution; and for every mild solution `u` and every `T > 0` there are a
probability space, a filtration, a Brownian motion `W`, a jointly measurable density version `ũ`
of `u` on `[0, T]` and a weak solution `X` of the McKean–Vlasov SDE (4.1)
`dX = b(X, ũ(t,X))dt + √2 σ(X, ũ(t,X))dW` on `[0, T]` with `X(0) ∼ u₀ dx` and
`Law(X(t)) = ũ(t,x)dx = u(t,x)dx` for `t ∈ [0, T]`. -/
theorem theorem_4_1 {d : ℕ} (σ : SDEState d → ℝ → Fin d → Fin d → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ)
    (hσ : ∀ i j, Measurable (fun p : SDEState d × ℝ => σ p.1 p.2 i j))
    (hb : ∀ i, Measurable (fun p : SDEState d × ℝ => b i p.1 p.2))
    (hyp : (∃ γ : ℝ, HypND (aOf σ) b γ) ∨
      ∃ (a' : Fin d → Fin d → ℝ → ℝ) (b' : Fin d → ℝ → ℝ),
        (∀ i j x r, aOf σ i j x r = a' i j r) ∧ (∀ i x r, b i x r = b' i r) ∧ HypDeg a' b')
    (u₀ : SDEState d →₁[volume] ℝ) (hu₀ : IsProbDensity u₀) :
    (∃ u : ℝ≥0 → SDEState d →₁[volume] ℝ, IsMildSolution (opA (aOf σ) b) u₀ u) ∧
    ∀ u : ℝ≥0 → SDEState d →₁[volume] ℝ, IsMildSolution (opA (aOf σ) b) u₀ u →
      ∀ T : ℝ≥0, 0 < T →
        ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
          (W X : ℝ≥0 → Ω → SDEState d) (ut : ℝ≥0 → SDEState d → ℝ),
          IsProbabilityMeasure P ∧
          Measurable (Function.uncurry ut) ∧
          (∀ t : ℝ≥0, t ≤ T → ut t =ᵐ[volume] (u t : SDEState d → ℝ)) ∧
          IsWeakSDESolution P ℱ
            (cutDiff T (fun t x i j => Real.sqrt 2 * σ x (ut t x) i j))
            (cutDrift T (fun t x i => b i x (ut t x)))
            (volume.withDensity (fun x => ENNReal.ofReal (u₀ x))) W X ∧
          ∀ t : ℝ≥0, t ≤ T →
            P.map (X t) = volume.withDensity (fun x => ENNReal.ofReal (ut t x)) := by sorry

end NonlinFPE.Main
