-- Prove2me | Theorems.Thm_ManIAL_theorem_3_6
-- name    : ManIAL.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:39.658991+00:00
-- url     : https://prove2.me/theorems/457b0e80-8272-4e29-94cb-248da2af4e16
-- title:
--   Theorem 3.6 — iteration complexity of ManIAL with Option II (corrected: $\sigma_k=2^{k/3}$; $K$ with $\sqrt{2c_2}$)
-- statement:
--   Suppose Assumption 1 holds. Let $(x^k,y^k,z^k)$ be a run of ManIAL with Option II and RGD as the subroutine, with $\sigma_k=2^{k/3}$, $\beta_0>0$, $x^0\in\mathcal M$, $y^0\in\mathbb R^m$ and a constant $G>0$ such that $\|\nabla\psi_k\|\le G$ on $\mathcal M$ for every $k$. Let $\underline\phi\le f(x)+h(\mathcal Ax-z^k/\sigma_k)\le\bar\phi$ for all $x\in\mathcal M$ and all $k$, and put
--
--   $$
--   z_{\max}=\frac{\beta_0\pi^2}6\|\mathcal Ax^0-y^0\|,\quad c_0=\bar\phi-\underline\phi+\frac{\ell_h^2+z_{\max}^2}2,\quad c_1=c_0\alpha^2\|\mathcal A\|^2,\quad c_2=c_0(\alpha^2\ell_{\nabla f}+2G\beta).
--   $$
--
--   Given $\epsilon>0$, for every integer
--
--   $$
--   K\ge3\log_2\frac{\sqrt{2c_1}+\sqrt{2c_2}+\ell_h+z_{\max}}{\epsilon},
--   $$
--
--   the triple $(x^{K+1},y^{K+1},\bar z^{K+1})$, $\bar z^{K+1}=z^K-\sigma_K(\mathcal Ax^{K+1}-y^{K+1})$, is an $\epsilon$-KKT point pair.
--
--   So ManIAL with Option II needs $O(\log(1/\epsilon))$ outer iterations, with $2^k$ RGD steps in iteration $k$.
--
--   Differences from the source:
--   - correction: σ_k = 1/2^{k/3} → σ_k = 2^{k/3}; reason: counterexample: M = S¹, A = I, h = ℓh‖·‖, f ≡ 0, y⁰ = Ax⁰; then z^k ≡ 0 and ‖Ax^{k+1} − y^{k+1}‖ = min(1, ℓh/σ_k) ≥ min(1, ℓh) when σ_k ≤ 1, so no iterate is ϵ-KKT for ϵ < min(1, ℓh); Algorithm 1 requires increasing σ_k and the proof of Theorem 3.6 uses σ_k = 2^{k/3}
--   - correction: K := log₂((√(2c₁) + ℓh + z_max)³/ϵ³) → every integer K ≥ 3 log₂((√(2c₁) + √(2c₂) + ℓh + z_max)/ϵ); reason: the proof's 'without loss of generality c₁2^{k/3} ≥ c₂' is not w.l.o.g.: M = S¹ with R_x(u) = (x+u)/‖x+u‖ (α = 1, β = 1/2), A = 0, h ≡ 0 with ℓh := ϵ, f(x) = c·x₂ (c ≥ 1, ℓ∇f = 1), G = c, x⁰ = (1,0), y⁰ = 0, β₀ = 1 gives c₁ = 0 and printed K = 0, but ‖P(∇f(x¹) − A*z̄¹)‖ ≥ c/√2 > ϵ for ϵ < 1/√2; with √(2c₂) and the factor 2 of Lemma 3.2 the proof goes through
--   - reading: c₁ 'defined in the proof'; ϕ̄, ϕ with ϕ ≤ f(x) + h(Ax − z^k/σ_k) ≤ ϕ̄ for x ∈ M, k ≥ 1 → c₀ = ϕ̄ − ϕ + (ℓh² + z_max²)/2, c₁ = c₀α²‖A‖², c₂ = c₀(α²ℓ∇f + 2Gβ) for any ϕ̄, ϕ bounding f + h(A· − z^k/σ_k) on M for every k ≥ 0; reason: the proof's definitions with σ₀ = 2⁰ = 1; the bound at k = 0 is used for x¹ (K can be 0) and exists by compactness
--   - reading: Option II: RGD returns x^{k+1} with 2^k iterations → x^{k+1} = u_t for any t ≤ 2^k minimizing ‖grad ψ_k(u_s)‖ over s ≤ 2^k; reason: Algorithm 2's output is an argmin; every tie-break is covered
--   - reading: the finite G of Lemma 3.3 (enters L_k) → any G > 0 with ‖∇ψ_k‖ ≤ G on M for every k of the run; reason: G enters the algorithm through the stepsize 1/L_k; the bound is what Lemma 3.3 uses
--   - generalization: M a compact Riemannian submanifold embedded in ℝⁿ with a retraction R → M any compact subset of ℝⁿ, T_xM the span of its tangent cone, R any map with R_x(T_xM) ⊆ M and the bounds (2.1) for some α, β > 0; reason: §3 uses (M, R) only through these properties; Proposition 2.2 gives them for every retraction on a compact submanifold, so the paper's setting is a special case
--   - generalization: y⁰ = Ax⁰ (Algorithm 1, step 2) → y⁰ arbitrary; reason: the bound (3.31) only uses (3.13); y⁰ = Ax⁰ is the special case (then z^k ≡ 0)
--   - reading: needs at most K iterations, K a real number → every integer K at least the printed value; reason: the integer iteration counts K ≥ the bound, including ⌈K⌉
--   - reading: dual step size β₀ → β₀ > 0; reason: a step size; (3.31) needs β₀ ≥ 0
--   - encoding: dist(−z, ∂h(y)) ≤ ϵ → ∃ g ∈ ∂h(y), ‖z + g‖ ≤ ϵ; reason: ∂h(y) is nonempty and compact for real-valued convex h, so the distance is attained
--   - encoding: log in (3.13); division by ‖Ax^{k+1} − y^{k+1}‖ = 0 → Real.log; Lean's x/0 = 0 gives β_{k+1} = 0; reason: β_{k+1} only enters through β_{k+1}(Ax^{k+1} − y^{k+1}) = 0, so the iterates are the same; (3.31) holds for the natural log
--   - encoding: Assumption 1: h : ℝᵐ → (−∞,+∞] proper closed convex and ℓh-Lipschitz; f ℓ∇f-smooth; ℝⁿ, ℝᵐ → h : ℝᵐ → ℝ convex with |h y − h y'| ≤ ℓh‖y − y'‖; f differentiable with ‖∇f x − ∇f x'‖ ≤ ℓ∇f‖x − x'‖; ℓ∇f, ℓh ≥ 0; EuclideanSpace ℝ (Fin n), (Fin m); reason: a Lipschitz h is finite everywhere, hence proper and closed; ℓ∇f-smooth means Lipschitz gradient; Lipschitz constants are nonnegative
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Theorem 3.6, p.13

import Mathlib
import Definitions.Def_ManIAL_RetrBounds
import Definitions.Def_ManIAL_psi
import Definitions.Def_ManIAL_zbar
import Definitions.Def_ManIAL_IsEpsKKT
import Definitions.Def_ManIAL_IsRunOptionII

namespace ManIAL

/-- **Theorem 3.6** (Iteration complexity of ManIAL with Option II) (Deng–Hu–Wu–Wen,
arXiv:2404.05121v2, p.13), corrected. Suppose Assumption 1 holds and let `(x^k, y^k, z^k)` be a
run of ManIAL with Option II and RGD as the subroutine, with `σ_k = 2^{k/3}` and a constant
`G > 0` that bounds `‖∇ψ_k‖` on `M` for every `k`. Let `ϕ ≤ f(x) + h(Ax − z^k/σ_k) ≤ ϕ̄` for all
`x ∈ M` and `k`, and put `z_max = (β₀π²/6)‖Ax⁰ − y⁰‖`,
`c₀ = ϕ̄ − ϕ + (ℓ_h² + z_max²)/2`, `c₁ = c₀α²‖A‖²`, `c₂ = c₀(α²ℓ_{∇f} + 2Gβ)`. Given `ϵ > 0`,
for every integer `K ≥ 3 log₂((√(2c₁) + √(2c₂) + ℓ_h + z_max)/ϵ)`, the triple
`(x^{K+1}, y^{K+1}, z̄^{K+1})` is an ϵ-KKT point pair.

**Formalization Note.** The printed statement has `σ_k = 1/2^{k/3}` and
`K = log₂((√(2c₁) + ℓ_h + z_max)³/ϵ³)`; both are false (the penalty must increase, and the
proof's "without loss of generality `c₁2^{k/3} ≥ c₂`" is not w.l.o.g.). The constants `c₀, c₁,
c₂` ("defined in the proof", with `σ₀ = 1`) and `z_max` are written out as hypotheses
`hzmax`–`hc₂`. Every integer `K` at least the bound works. -/
theorem theorem_3_6 {n m : ℕ} (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsCompact M)
    (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hR : RetrBounds M R α β)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ℓf : ℝ) (hℓf : 0 ≤ ℓf) (hf : Differentiable ℝ f)
    (hfL : ∀ x x', ‖gradient f x - gradient f x'‖ ≤ ℓf * ‖x - x'‖)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (ℓh : ℝ) (hℓh : 0 ≤ ℓh) (hh : ConvexOn ℝ Set.univ h)
    (hhL : ∀ y y', |h y - h y'| ≤ ℓh * ‖y - y'‖)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hφ : BddBelow ((fun x => f x + h (A x)) '' M))
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (y₀ : EuclideanSpace ℝ (Fin m))
    (β₀ : ℝ) (hβ₀ : 0 < β₀) (G : ℝ) (hG : 0 < G)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m)) (N : ℕ → ℕ)
    (hrun : IsRunOptionII M R f h A α β ℓf G β₀ x₀ y₀ x y z N)
    (hGb : ∀ k : ℕ, ∀ u ∈ M, ‖gradient (psi f h A ((2 : ℝ) ^ ((k : ℝ) / 3)) (z k)) u‖ ≤ G)
    (ϕlo ϕhi : ℝ)
    (hϕ : ∀ k : ℕ, ∀ u ∈ M,
      ϕlo ≤ f u + h (A u - ((2 : ℝ) ^ ((k : ℝ) / 3))⁻¹ • z k) ∧
      f u + h (A u - ((2 : ℝ) ^ ((k : ℝ) / 3))⁻¹ • z k) ≤ ϕhi)
    (zmax c₀ c₁ c₂ : ℝ) (hzmax : zmax = β₀ * Real.pi ^ 2 / 6 * ‖A x₀ - y₀‖)
    (hc₀ : c₀ = ϕhi - ϕlo + (ℓh ^ 2 + zmax ^ 2) / 2) (hc₁ : c₁ = c₀ * α ^ 2 * ‖A‖ ^ 2)
    (hc₂ : c₂ = c₀ * (α ^ 2 * ℓf + 2 * G * β))
    (ε : ℝ) (hε : 0 < ε) (K : ℕ)
    (hK : 3 * Real.logb 2
      ((Real.sqrt (2 * c₁) + Real.sqrt (2 * c₂) + ℓh + zmax) / ε) ≤ K) :
    IsEpsKKT M f h A ε (x (K + 1)) (y (K + 1))
      (zbar ((2 : ℝ) ^ ((K : ℝ) / 3)) (z K) A (x (K + 1)) (y (K + 1))) := by sorry

end ManIAL
