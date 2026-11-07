-- Prove2me | Theorems.Thm_MatMulTimeLP_theorem_5_4
-- name    : MatMulTimeLP.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:04.044204+00:00
-- url     : https://prove2.me/theorems/d222a376-43ec-454e-a460-bbdd4313e998
-- title:
--   Theorem 5.4 — one step of coordinate mirror descent contracts $D_\Psi(a,z)$
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^n$ have a zero $a$ and be $\beta$-co-coercive, with $\beta>0$. Let $\psi_i:\mathbb R\to\mathbb R$ be differentiable and strictly convex, $\Psi(z)=\sum_i\psi_i(z_i)$, and suppose $F$ is $\mu$-strongly monotone relative to $D_\Psi$. Fix $z$ and $\sigma_i>0$, choose $\Lambda\ge\sum_i\sigma_i^{-1}$, set $p_i=\sigma_i^{-1}/\Lambda$ and $\eta=\beta/(4\Lambda)$. For each $i$ let $\hat z_i$ satisfy $\psi_i'(\hat z_i)=\psi_i'(z_i)-\frac{\eta}{p_i}F_i(z)$, and suppose $\psi_i$ is $\sigma_i/2$-strongly convex on the interval between $z_i$ and $\hat z_i$. If $z'$ replaces $z_i$ by $\hat z_i$ with probability $p_i$, and $z'=z$ with the remaining probability, then
--
--   $$\mathbb E[D_\Psi(a,z')]\le\Bigl(1-\frac{\beta\mu}{8\Lambda}\Bigr)D_\Psi(a,z)-\frac{\beta^2}{16\Lambda}\|F(z)\|_2^2.$$
--
--   This is the engine of the fix point algorithm: sampling coordinates by their local smoothness makes the rate depend on $\sum_i\sigma_i^{-1}$ rather than on the worst coordinate.
--
--   **Formalization Note** The expectation is the finite sum over the selected coordinate. Mathlib's `StrongConvexOn s m` is the paper's $m$-strong convexity (p.21).
--
--   Differences from the source:
--   - reading: $\beta$-co-coercive, with no stated sign → `0 < β`; reason: the paper's standing use (Claim 2.5, p.9, says $\beta,\mu>0$); at $\beta<0$ the step reverses, $\eta<0$
--   - generalization: $\mu>0$ (Claim 2.5, p.9) → `μ : ℝ` unconstrained; reason: the proof does not use a sign, and every $\mu>0$ is an instance
--   - encoding: "$\psi_i'(z_i)-\frac{\eta}{p_i}F_i(z)$ lies in the range of $\psi_i'$" and $\hat z_i=(\psi_i')^{-1}(\cdot)$ → a point `zhat i` satisfying that equation, with `dψ i` the derivative; reason: equivalent; `zhat i` is unique by strict convexity
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Theorem 5.4, p.23; Definitions 2.3, 2.7, pp.8, 10

import Mathlib
import Definitions.Def_MatMulTimeLP_FixPoint

namespace MatMulTimeLP

open Matrix

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Theorem 5.4, p.23 (coordinate mirror descent, one step):
`E[D_Ψ(a, z')] ≤ (1 - βμ/(8Λ)) D_Ψ(a, z) - β²/(16Λ) ‖F(z)‖₂²`.

**Formalization Note** The expectation is the finite sum over the selected coordinate, with the remaining
probability on `z' = z`. `dψ i` is the derivative of `ψ i`; "`ψ'ᵢ(zᵢ) - (η/pᵢ)Fᵢ(z)` lies in the range of `ψ'ᵢ`, and `ẑᵢ`
is the inverse image" is the existence of `zhat` with that equation (unique by strict convexity).
`StrongConvexOn s (σᵢ/2)` is the paper's `σᵢ/2`-strong convexity (p.21). `0 < β` is the standing reading of
co-coercivity (Claim 2.5, p.9); `μ` may have any sign, which is more than the page assumes. -/
theorem theorem_5_4 {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ) (a : Fin n → ℝ) (hFa : F a = 0)
    (β : ℝ) (hβ : 0 < β) (hco : IsCoCoercive F β) (ψ dψ : Fin n → ℝ → ℝ)
    (hd : ∀ i t, HasDerivAt (ψ i) (dψ i t) t) (hsc : ∀ i, StrictConvexOn ℝ Set.univ (ψ i))
    (μ : ℝ) (hμ : IsRelStronglyMonotone F (bregmanSep ψ dψ) μ) (z σ : Fin n → ℝ)
    (hσ : ∀ i, 0 < σ i) (lam : ℝ) (hlam : ∑ i, (σ i)⁻¹ ≤ lam) (zhat : Fin n → ℝ)
    (hzhat : ∀ i, dψ i (zhat i) = dψ i (z i) - β / (4 * lam) / ((σ i)⁻¹ / lam) * F z i)
    (hconv : ∀ i, StrongConvexOn (Set.uIcc (z i) (zhat i)) (σ i / 2) (ψ i)) :
    ∑ i, (σ i)⁻¹ / lam * bregmanSep ψ dψ a (Function.update z i (zhat i)) +
        (1 - ∑ i, (σ i)⁻¹ / lam) * bregmanSep ψ dψ a z ≤
      (1 - β * μ / (8 * lam)) * bregmanSep ψ dψ a z - β ^ 2 / (16 * lam) * (F z ⬝ᵥ F z) := by sorry

end MatMulTimeLP
