-- Prove2me | Theorems.Thm_ManIAL_eq_3_36_3_37
-- name    : ManIAL.eq_3_36_3_37
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:21.58008+00:00
-- url     : https://prove2.me/theorems/85c31b3c-1740-44bd-93a1-679e520453ef
-- title:
--   Displays (3.36)–(3.37) — uniform bound on $\psi_k(x^k)-\psi_{k,\min}$
-- statement:
--   Suppose Assumption 1 holds, and let $\sigma_0>0$ and $z_{\max}\ge0$. For every $\sigma\ge\sigma_0$ and every $z$ with $\|z\|\le z_{\max}$, write $\psi=\mathcal L_\sigma(\cdot,z)$. Then
--
--   1. (3.36) for every $x$:
--   $$
--   \psi(x)\le f(x)+h(\mathcal Ax-z/\sigma)\le\psi(x)+\frac{\ell_h^2+z_{\max}^2}{2\sigma_0};
--   $$
--   2. there are constants $\underline\phi,\bar\phi$ with $\underline\phi\le f(x)+h(\mathcal Ax-z/\sigma)\le\bar\phi$ for all $x\in\mathcal M$, all $\sigma\ge\sigma_0$ and all $\|z\|\le z_{\max}$;
--   3. (3.37) whenever $\underline\phi\le f+h(\mathcal A\cdot-z/\sigma)\le\bar\phi$ on $\mathcal M$,
--   $$
--   \psi(x)-\psi(x')\le\bar\phi-\underline\phi+\frac{\ell_h^2+z_{\max}^2}{2\sigma_0}\qquad\text{for all }x,x'\in\mathcal M,
--   $$
--   that is, $\psi(x)-\inf_{\mathcal M}\psi$ is bounded by the right-hand side.
--
--   With $z=z^k$ (bounded by (3.31)) and $\sigma=\sigma_k$, this bounds the optimality gap $\psi_k(x^k)-\psi_{k,\min}$ uniformly in $k$, which enters every inner iteration count.
--
--   Differences from the source:
--   - generalization: σ_k > σ₀, z = z^k bounded by z_max, k ≥ 1 → every σ ≥ σ₀ > 0 and every z with ‖z‖ ≤ z_max; reason: contains every iterate
--   - generalization: M a compact Riemannian submanifold embedded in ℝⁿ (with a retraction) → M any compact subset of ℝⁿ, T_xM the span of its tangent cone, no retraction; reason: the proof uses only compactness of M and the Moreau envelope bounds; a compact submanifold is a special case
--   - encoding: ψ_k(x^k) − ψ_{k,min}, ψ_{k,min} = inf_{x∈M} ψ_k(x) → ψ(x) − ψ(x') for all x, x' ∈ M; reason: the same bound (M is nonempty in use), without Lean's junk value of a real infimum
--   - encoding: ‖z_max‖², ℓ²h → zmax ^ 2, ℓh ^ 2; reason: notation
--   - encoding: Assumption 1: h : ℝᵐ → (−∞,+∞] proper closed convex and ℓh-Lipschitz; f ℓ∇f-smooth; ℝⁿ, ℝᵐ → h : ℝᵐ → ℝ convex with |h y − h y'| ≤ ℓh‖y − y'‖; f differentiable with ‖∇f x − ∇f x'‖ ≤ ℓ∇f‖x − x'‖; ℓ∇f, ℓh ≥ 0; EuclideanSpace ℝ (Fin n), (Fin m); reason: a Lipschitz h is finite everywhere, hence proper and closed; ℓ∇f-smooth means Lipschitz gradient; Lipschitz constants are nonnegative
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, displays (3.36)–(3.37), p.13

import Mathlib
import Definitions.Def_ManIAL_psi

namespace ManIAL

/-- **Displays (3.36)–(3.37)** (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.13): the gap
`ψ_k(x^k) − ψ_{k,min}` is uniformly bounded. Under Assumption 1, let `σ₀ > 0` and `z_max ≥ 0`.
For every `σ ≥ σ₀` and `‖z‖ ≤ z_max`, with `ψ = 𝓛_σ(·, z)`:
1. (3.36) `ψ(x) ≤ f(x) + h(Ax − z/σ) ≤ ψ(x) + (ℓ_h² + z_max²)/(2σ₀)` for every `x`;
2. there are `ϕ ≤ ϕ̄` with `ϕ ≤ f(x) + h(Ax − z/σ) ≤ ϕ̄` for all `x ∈ M`, all `σ ≥ σ₀` and all
   `‖z‖ ≤ z_max`;
3. (3.37) whenever `ϕ ≤ f + h(A· − z/σ) ≤ ϕ̄` on `M`,
   `ψ(x) − ψ(x') ≤ ϕ̄ − ϕ + (ℓ_h² + z_max²)/(2σ₀)` for all `x, x' ∈ M`.

**Formalization Note.** Item 3 for all `x' ∈ M` is the printed bound on `ψ_k(x^k) − ψ_{k,min}`
with `ψ_{k,min} = inf_M ψ_k` (it avoids Lean's junk value of a real infimum). The paper takes
`σ_k > σ₀`; `σ ≥ σ₀` is allowed here. -/
theorem eq_3_36_3_37 {n m : ℕ} (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsCompact M)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ℓf : ℝ) (hℓf : 0 ≤ ℓf) (hf : Differentiable ℝ f)
    (hfL : ∀ x x', ‖gradient f x - gradient f x'‖ ≤ ℓf * ‖x - x'‖)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (ℓh : ℝ) (hℓh : 0 ≤ ℓh) (hh : ConvexOn ℝ Set.univ h)
    (hhL : ∀ y y', |h y - h y'| ≤ ℓh * ‖y - y'‖)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hφ : BddBelow ((fun x => f x + h (A x)) '' M))
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (zmax : ℝ) (hzmax : 0 ≤ zmax) :
    (∀ σ : ℝ, σ₀ ≤ σ → ∀ z : EuclideanSpace ℝ (Fin m), ‖z‖ ≤ zmax →
      ∀ x : EuclideanSpace ℝ (Fin n),
        psi f h A σ z x ≤ f x + h (A x - σ⁻¹ • z) ∧
        f x + h (A x - σ⁻¹ • z) ≤ psi f h A σ z x + (ℓh ^ 2 + zmax ^ 2) / (2 * σ₀)) ∧
    (∃ ϕlo ϕhi : ℝ, ∀ σ : ℝ, σ₀ ≤ σ → ∀ z : EuclideanSpace ℝ (Fin m), ‖z‖ ≤ zmax →
      ∀ x ∈ M, ϕlo ≤ f x + h (A x - σ⁻¹ • z) ∧ f x + h (A x - σ⁻¹ • z) ≤ ϕhi) ∧
    (∀ σ : ℝ, σ₀ ≤ σ → ∀ z : EuclideanSpace ℝ (Fin m), ‖z‖ ≤ zmax → ∀ ϕlo ϕhi : ℝ,
      (∀ x ∈ M, ϕlo ≤ f x + h (A x - σ⁻¹ • z) ∧ f x + h (A x - σ⁻¹ • z) ≤ ϕhi) →
      ∀ x ∈ M, ∀ x' ∈ M,
        psi f h A σ z x - psi f h A σ z x' ≤ ϕhi - ϕlo + (ℓh ^ 2 + zmax ^ 2) / (2 * σ₀)) := by sorry

end ManIAL
