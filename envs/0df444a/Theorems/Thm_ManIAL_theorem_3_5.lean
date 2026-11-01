-- Prove2me | Theorems.Thm_ManIAL_theorem_3_5
-- name    : ManIAL.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:59.67799+00:00
-- url     : https://prove2.me/theorems/386d9e9d-61b4-4f8e-b4c0-4357f199ff56
-- title:
--   Theorem 3.5 — iteration complexity of ManIAL with Option I
-- statement:
--   Suppose Assumption 1 holds. Let $b>1$, $\sigma_k=b^k$, $\epsilon_k=1/\sigma_k$, $\beta_0>0$, $x^0\in\mathcal M$, $y^0\in\mathbb R^m$, and let $(x^k,y^k,z^k)$ follow the outer recursion of ManIAL with Option I: each $x^{k+1}\in\mathcal M$ satisfies $\|\operatorname{grad}\psi_k(x^{k+1})\|\le\epsilon_k$ (3.12), whatever subroutine produced it. Let $z_{\max}=\frac{\beta_0\pi^2}6\|\mathcal Ax^0-y^0\|$ and $\bar z^{K+1}=z^K-\sigma_K(\mathcal Ax^{K+1}-y^{K+1})$. Given $\epsilon>0$, for every integer
--
--   $$
--   K\ge\log_b\frac{\ell_h+z_{\max}+1}{\epsilon},
--   $$
--
--   the triple $(x^{K+1},y^{K+1},\bar z^{K+1})$ is an $\epsilon$-KKT point pair (3.4).
--
--   So ManIAL with Option I needs $O(\log(1/\epsilon))$ outer iterations, independently of how the subproblems are solved.
--
--   Differences from the source:
--   - generalization: y⁰ = Ax⁰ (Algorithm 1, step 2) → y⁰ arbitrary; reason: the bound (3.31) only uses (3.13); y⁰ = Ax⁰ is the special case (then z^k ≡ 0)
--   - generalization: M a compact Riemannian submanifold embedded in ℝⁿ (with a retraction) → M any compact subset of ℝⁿ, T_xM the span of its tangent cone, no retraction; reason: the proof uses only (3.12), (3.15) and the prox step at the given points of M; a compact submanifold, whose tangent space is the span of its tangent cone, is a special case
--   - reading: needs at most K iterations, K a real number → every integer K at least the printed value; reason: the integer iteration counts K ≥ the bound, including ⌈K⌉
--   - reading: dual step size β₀ → β₀ > 0; reason: a step size; (3.31) needs β₀ ≥ 0
--   - encoding: ‖z_max‖ → z_max (a nonnegative number, given by hzmax); reason: z_max is a scalar
--   - encoding: x^{k+1} returned by a subroutine on M → x^{k+1} ∈ M as a hypothesis; reason: the subroutine of Algorithm 1 works on M
--   - encoding: dist(−z, ∂h(y)) ≤ ϵ → ∃ g ∈ ∂h(y), ‖z + g‖ ≤ ϵ; reason: ∂h(y) is nonempty and compact for real-valued convex h, so the distance is attained
--   - encoding: log in (3.13); division by ‖Ax^{k+1} − y^{k+1}‖ = 0 → Real.log; Lean's x/0 = 0 gives β_{k+1} = 0; reason: β_{k+1} only enters through β_{k+1}(Ax^{k+1} − y^{k+1}) = 0, so the iterates are the same; (3.31) holds for the natural log
--   - encoding: Assumption 1: h : ℝᵐ → (−∞,+∞] proper closed convex and ℓh-Lipschitz; f ℓ∇f-smooth; ℝⁿ, ℝᵐ → h : ℝᵐ → ℝ convex with |h y − h y'| ≤ ℓh‖y − y'‖; f differentiable with ‖∇f x − ∇f x'‖ ≤ ℓ∇f‖x − x'‖; ℓ∇f, ℓh ≥ 0; EuclideanSpace ℝ (Fin n), (Fin m); reason: a Lipschitz h is finite everywhere, hence proper and closed; ℓ∇f-smooth means Lipschitz gradient; Lipschitz constants are nonnegative
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Theorem 3.5, display (3.27), pp.11–12

import Mathlib
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ManIAL_psi
import Definitions.Def_ManIAL_zbar
import Definitions.Def_ManIAL_IsEpsKKT
import Definitions.Def_ManIAL_IsManIALIterates

open ZORiem.RGD

namespace ManIAL

/-- **Theorem 3.5** (Iteration complexity of ManIAL with Option I) (Deng–Hu–Wu–Wen,
arXiv:2404.05121v2, pp.11–12). Suppose Assumption 1 holds, `b > 1`, `σ_k = b^k`,
`ϵ_k = 1/σ_k`, and let `(x^k, y^k, z^k)` follow Algorithm 1 with Option I: `x^{k+1} ∈ M` with
`‖grad ψ_k(x^{k+1})‖ ≤ ϵ_k` (3.12), produced by any subroutine. Given `ϵ > 0`, for every integer
`K ≥ log_b((ℓ_h + z_max + 1)/ϵ)`, with `z_max = (β₀π²/6)‖Ax⁰ − y⁰‖` and
`z̄^{K+1} = z^K − σ_K(Ax^{K+1} − y^{K+1})` (3.27), `(x^{K+1}, y^{K+1}, z̄^{K+1})` is an ϵ-KKT
point pair (3.4).

**Formalization Note.** "Needs at most `K` iterations", with `K` real, is read as: every integer
`K` at least the printed value works. `y⁰` is arbitrary (the paper sets `y⁰ = Ax⁰`), `β₀ > 0` is
the dual step size, and `z_max` is written out (`hzmax`). The sequence `x` is arbitrary apart from
(3.12) and `x^{k+1} ∈ M` ("without specifying a subroutine", p.11). -/
theorem theorem_3_5 {n m : ℕ} (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsCompact M)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ℓf : ℝ) (hℓf : 0 ≤ ℓf) (hf : Differentiable ℝ f)
    (hfL : ∀ x x', ‖gradient f x - gradient f x'‖ ≤ ℓf * ‖x - x'‖)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (ℓh : ℝ) (hℓh : 0 ≤ ℓh) (hh : ConvexOn ℝ Set.univ h)
    (hhL : ∀ y y', |h y - h y'| ≤ ℓh * ‖y - y'‖)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hφ : BddBelow ((fun x => f x + h (A x)) '' M))
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (y₀ : EuclideanSpace ℝ (Fin m))
    (β₀ : ℝ) (hβ₀ : 0 < β₀) (b : ℝ) (hb : 1 < b)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hit : IsManIALIterates h A β₀ (fun k => b ^ k) x₀ y₀ x y z)
    (hxM : ∀ k : ℕ, x (k + 1) ∈ M)
    (hopt : ∀ k : ℕ, ‖rgrad M (psi f h A (b ^ k) (z k)) (x (k + 1))‖ ≤ 1 / b ^ k)
    (zmax : ℝ) (hzmax : zmax = β₀ * Real.pi ^ 2 / 6 * ‖A x₀ - y₀‖)
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) (hK : Real.logb b ((ℓh + zmax + 1) / ε) ≤ K) :
    IsEpsKKT M f h A ε (x (K + 1)) (y (K + 1))
      (zbar (b ^ K) (z K) A (x (K + 1)) (y (K + 1))) := by sorry

end ManIAL
