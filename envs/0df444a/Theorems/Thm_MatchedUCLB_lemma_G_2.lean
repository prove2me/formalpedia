-- Prove2me | Theorems.Thm_MatchedUCLB_lemma_G_2
-- name    : MatchedUCLB.lemma_G_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:12.597776+00:00
-- url     : https://prove2.me/theorems/0a0cc1fc-85a9-46b4-a82a-9680f44f71b6
-- title:
--   Lemma G.2 — the critical rescaling $\hat F(x)=a^qF((x-x_0)/a)$ preserves $H$, $\sigma$ and rescales the gap by $a^q$
-- statement:
--   Let $q=p+\nu$ with $p\ge2$, $0<\nu\le1$, let $F:\mathbb R^d\to\mathbb R$ be $p$ times continuously differentiable, $a>0$, $x_0\in\mathbb R^d$, and
--
--   $$
--   \hat F(x)=a^q\,F\Bigl(\frac{x-x_0}{a}\Bigr).
--   $$
--
--   Then:
--
--   1. $\nabla^k\hat F(x)=a^{q-k}\nabla^kF\bigl(\frac{x-x_0}a\bigr)$ for $0\le k\le p$;
--   2. every $p$th-order Hölder parameter $H$ of $F$ (exponent $\nu$) is one of $\hat F$;
--   3. $D_{\hat F}(y,x)=a^qD_F\bigl(\frac{y-x_0}a,\frac{x-x_0}a\bigr)$ (G.1);
--   4. every degree-$q$ uniform-convexity modulus $\sigma$ of $F$ is one of $\hat F$;
--   5. the minimizers of $\hat F$ are $x_0+a\cdot\operatorname{argmin}F$;
--   6. for a minimizer $x_\star$ of $F$, $\hat F(x_0)-\hat F(x_0+ax_\star)=a^q\bigl(F(0)-F(x_\star)\bigr)$, and if $\Delta_0>0$, $F(0)-F(x_\star)>0$ and $a=\bigl(\Delta_0/(F(0)-F(x_\star))\bigr)^{1/q}$, this gap equals $\Delta_0$.
--
--   Because $q=p+\nu$, the rescaling leaves both class parameters unchanged while setting the initial gap to any prescribed $\Delta_0$ and moving the start to any $x_0$. For the complete objective, $\operatorname{argmin}F=\{c_L\}$ and $F(0)-F(c_L)=D_{m,L}$ (Lemma 4.5), which gives the printed $\operatorname{argmin}\hat F=\{x_0+ac_L\}$ and $\hat F(x_0)-\min\hat F=a^qD_{m,L}$.
--
--   **Formalization Note** $D_F$ is the published Bregman divergence `AdaGradDHS.Diag.bregman`.
--
--   Differences from the source:
--   - encoding: ℝ^d, ∇^kF, ⟨∇F(x), v⟩ → EuclideanSpace ℝ (Fin d), iteratedFDeriv ℝ k F, fderiv ℝ F x v; reason: Lean convention; the norm of iteratedFDeriv is the operator norm of Sec. 3; same instances
--   - encoding: q = p + ν → a real binder q with the hypothesis hq : q = p + ν; reason: notation only; every instance has q = p + ν
--   - generalization: F the complete objective of Definition E.8 → every F : ℝ^d → ℝ with ContDiff ℝ p F; reason: the proof uses only the chain rule; the objective is C^p by Lemma 4.5(a), so the printed lemma is the instance
--   - generalization: argmin F̂ = {x_0 + ac_L}, F̂(x_0) − min F̂ = a^qD_{m,L} → argmin F̂ = (x_0 + a·) '' argmin F, and F̂ x_0 − F̂(x_0 + a•x⋆) = a^q(F 0 − F x⋆) at any minimizer x⋆ of F; reason: for the objective, argmin F = {c_L} and F(0) − F(c_L) = D_{m,L} (Lemma 4.5(b),(d), c_0 = 0), which gives the printed formulas
--   - reading: a = (Δ_0/D_{m,L})^{1/q} gives F̂(x_0) − min F̂ = Δ_0 → the clause assumes 0 < Δ_0 and 0 < F 0 − F x⋆; reason: Δ_0 > 0 is the prescribed initial gap of Theorem 1.1 and D_{m,L} > 0 by Lemma 4.5(d); without them the real power is not the intended one
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma G.2, p.108, Eq. (G.1)

import Mathlib
import Definitions.Def_MatchedUCLB_HolderBound
import Definitions.Def_MatchedUCLB_UnifConvex
import Definitions.Def_AdaGradDHS_Diag_bregman

open scoped ContDiff Topology

namespace MatchedUCLB

/-- **Lemma G.2 (rescaling preserves the critical class).** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma G.2, p.108: "Let `F` be the
objective in Definition E.8. For `a > 0` and an initialization `x_0`, define `F_a(x) := a^qF(x/a)`,
`F̂(x) := F_a(x − x_0)`. For `0 ≤ k ≤ p`, with `∇^0F = F`, `∇^kF̂(x) = a^{q−k}∇^kF((x − x_0)/a)`. Every
pth-order Hölder smoothness parameter `H` of `F` is preserved: for all `x, y`,
`‖∇^pF̂(x) − ∇^pF̂(y)‖ ≤ H‖x − y‖^ν`, `D_F̂(y, x) = a^qD_F((y − x_0)/a, (x − x_0)/a)` (G.1). Every
admissible degree-q uniform-convexity modulus is preserved, and `argmin F̂ = {x_0 + ac_L}`,
`F̂(x_0) − min F̂ = a^qD_{m,L}`. In particular, `a = (Δ_0/D_{m,L})^{1/q}` gives `F̂(x_0) − min F̂ = Δ_0`."

**Formalization Note.** `q` is a separate real binder with the hypothesis `q = p + ν` (the matched order of the paper), so that every formula can be written in `q`. The lemma is stated for every `p` times continuously differentiable
`F : ℝ^d → ℝ` (a generalization; the objective of Definition E.8 is one, by Lemma 4.5(a)).
`F̂(x) = a^q F(a⁻¹(x − x_0))`. The argmin statement is `argmin F̂ = x_0 + a · argmin F`; with
`argmin F = {c_L}` (Lemma 4.5(b)) it is the printed `{x_0 + ac_L}`. The gap statement is written at
a minimizer `x⋆` of `F`, whose image `x_0 + ax⋆` minimizes `F̂`, with `F(0) − F(x⋆)` in place of
`D_{m,L} = F(c_0) − F(c_L)` (`c_0 = 0`); the last clause takes `Δ_0 > 0` and `F(0) − F(x⋆) > 0`, as in
the paper. `D_F` is the published Bregman divergence `AdaGradDHS.Diag.bregman`. -/
theorem lemma_G_2 (p : ℕ) (hp : 2 ≤ p) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (q : ℝ) (hq : q = (p : ℝ) + ν) {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ContDiff ℝ p F) (a : ℝ) (ha : 0 < a)
    (x₀ : EuclideanSpace ℝ (Fin d)) :
    (∀ k : ℕ, k ≤ p → ∀ x : EuclideanSpace ℝ (Fin d),
      iteratedFDeriv ℝ k (fun x : EuclideanSpace ℝ (Fin d) => a ^ q * F (a⁻¹ • (x - x₀))) x = a ^ (q - k) • iteratedFDeriv ℝ k F (a⁻¹ • (x - x₀))) ∧
    (∀ H : ℝ, HolderBound p ν H F → HolderBound p ν H (fun x : EuclideanSpace ℝ (Fin d) => a ^ q * F (a⁻¹ • (x - x₀)))) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d), AdaGradDHS.Diag.bregman (fun x : EuclideanSpace ℝ (Fin d) => a ^ q * F (a⁻¹ • (x - x₀))) y x =
      a ^ q * AdaGradDHS.Diag.bregman F (a⁻¹ • (y - x₀)) (a⁻¹ • (x - x₀))) ∧
    (∀ σ : ℝ, UnifConvex q σ F → UnifConvex q σ (fun x : EuclideanSpace ℝ (Fin d) => a ^ q * F (a⁻¹ • (x - x₀)))) ∧
    {x : EuclideanSpace ℝ (Fin d) | ∀ y : EuclideanSpace ℝ (Fin d), (fun x : EuclideanSpace ℝ (Fin d) => a ^ q * F (a⁻¹ • (x - x₀))) x ≤ (fun x : EuclideanSpace ℝ (Fin d) => a ^ q * F (a⁻¹ • (x - x₀))) y} = (fun z : EuclideanSpace ℝ (Fin d) => x₀ + a • z) '' {z : EuclideanSpace ℝ (Fin d) | ∀ y : EuclideanSpace ℝ (Fin d), F z ≤ F y} ∧
    (∀ xs : EuclideanSpace ℝ (Fin d), (∀ y : EuclideanSpace ℝ (Fin d), F xs ≤ F y) → (fun x : EuclideanSpace ℝ (Fin d) => a ^ q * F (a⁻¹ • (x - x₀))) x₀ - (fun x : EuclideanSpace ℝ (Fin d) => a ^ q * F (a⁻¹ • (x - x₀))) (x₀ + a • xs) = a ^ q * (F 0 - F xs)) ∧
    (∀ (xs : EuclideanSpace ℝ (Fin d)) (Δ₀ : ℝ), (∀ y : EuclideanSpace ℝ (Fin d), F xs ≤ F y) → 0 < Δ₀ → 0 < F 0 - F xs →
      a = (Δ₀ / (F 0 - F xs)) ^ (1 / q) → (fun x : EuclideanSpace ℝ (Fin d) => a ^ q * F (a⁻¹ • (x - x₀))) x₀ - (fun x : EuclideanSpace ℝ (Fin d) => a ^ q * F (a⁻¹ • (x - x₀))) (x₀ + a • xs) = Δ₀) := by sorry

end MatchedUCLB
