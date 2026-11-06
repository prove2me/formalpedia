-- Prove2me | Theorems.Thm_HOTrap_lemma_A_4
-- name    : HOTrap.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:48:03.277532+00:00
-- url     : https://prove2.me/theorems/877b2bff-3435-45af-9da7-3759fabb9aef
-- title:
--   Lemma A.4 — interpolation error and stability
-- statement:
--   Let $C\subset\mathbb R^d$ be nonempty, compact and convex, let $P$ be an $n$-dimensional real polynomial space with $n\ge1$, and let $z_1,\dots,z_n\in C$ be unisolvent for $P$ with Lagrange basis $\ell_i$. Let $F$ be continuous on $C$, let $\|\tilde F_i-F(z_i)\|\le\tau$ with $\tau\ge0$, and put $I=\sum_i\tilde F_i\ell_i$. With $\Lambda_0=\sup_{y\in C}\sum_i|\ell_i(y)|$ and $\Lambda_1=\sup_{y\in C}\sum_i\|\nabla\ell_i(y)\|_2$, every polynomial map $T$ with components in $P$ and nodal error $r_T=\max_i\|F(z_i)-T(z_i)\|$ satisfies
--   $$
--   \|I-F\|_{\infty,C}\le\|T-F\|_{\infty,C}+\Lambda_0(r_T+\tau),\qquad\|DI-DF\|_{\infty,C}\le\|DT-DF\|_{\infty,C}+\Lambda_1(r_T+\tau),
--   $$
--   the second bound when $F$ is continuously differentiable near $C$. If $\Pi^d_p\subseteq P$ and $F\in C^{p,\beta}(L)$ near $C$, then
--   $$
--   \|I-F\|_{\infty,C}\le(1+\Lambda_0)\,a_{p,\beta}\,L\,\mathrm{diam}(C)^{p+\beta}+\Lambda_0\tau,
--   $$
--   including $p=0$.
--
--   This lemma converts errors in supplied values into errors of the interpolant; it controls the separator models and the line-integration rule.
--
--   Differences from the source:
--   - generalization: F scalar- or vector-valued, with Euclidean output norms → F takes values in any real Banach space G; reason: ℝ and ℝ^m are Banach spaces, so the printed statement is the instance G = ℝ^m
--   - encoding: "on a neighborhood of S" → an open set U containing S; reason: the standard meaning of the phrase
--   - encoding: sup norms and the stability constants Λ₀, Λ₁ → pointwise bounds and arbitrary upper bounds of the same quantities; reason: a bound for every upper bound is equivalent to the bound at the supremum, and avoids a junk real sSup
--   - encoding: an n-dimensional real polynomial space P → a submodule Q of the polynomial functions with finrank n; reason: polynomials and polynomial functions on ℝ^d are identified, as in the paper
--   - encoding: the maximum nodal error r_T := max_i ∥F(z_i) − T(z_i)∥ → an arbitrary upper bound r of the nodal errors; reason: a bound for every upper bound is equivalent to the bound at the maximum
--   - encoding: a comparison polynomial map T whose components belong to P → IsPolyMap Q T, a finite sum y ↦ ∑ₖ φₖ(y) gₖ with φₖ ∈ Q and gₖ ∈ G; reason: for G = ℝ or ℝ^m this is exactly "each component lies in P", and it is the meaning of the phrase for a general G
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Lemma A.4, Eqs. (55), (56), p.55, with the setup of p.54

import Mathlib
import Definitions.Def_HOTrap_HolderNear
import Definitions.Def_HOTrap_CkNear
import Definitions.Def_HOTrap_taylorConst
import Definitions.Def_HOTrap_polyEval
import Definitions.Def_HOTrap_PolyLE
import Definitions.Def_HOTrap_IsPolyMap
import Definitions.Def_HOTrap_IsUnisolvent
import Definitions.Def_HOTrap_IsLagrangeBasis
import Definitions.Def_HOTrap_interpolant

namespace HOTrap

/-- **Lemma A.4 (interpolation error and stability).** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Lemma A.4, Eqs. (55), (56), p.55, in the setup
of p.54: `C ⊂ ℝ^d` nonempty, compact, convex; `P` an `n`-dimensional real polynomial space, `n ≥ 1`; nodes
`z₁,…,zₙ ∈ C` unisolvent for `P` with Lagrange basis `ℓᵢ`; `F` continuous on `C`; supplied values with
`∥F̃ᵢ − F(zᵢ)∥ ≤ τ`; `I = ∑ᵢ F̃ᵢ ℓᵢ`. Every comparison polynomial map `T` with components in `P` satisfies
`∥I − F∥_{∞,C} ≤ ∥T − F∥_{∞,C} + Λ₀(r_T + τ)`, and, if `F` is `C¹` near `C`,
`∥DI − DF∥_{∞,C} ≤ ∥DT − DF∥_{∞,C} + Λ₁(r_T + τ)`. If `Π^d_p ⊆ P` and `F ∈ C^{p,β}(L)` near `C`, then
`∥I − F∥_{∞,C} ≤ (1 + Λ₀) a_{p,β} L diam(C)^{p+β} + Λ₀ τ`, including `p = 0`.

**Formalization Note** `P` is `Q`, a submodule of the polynomial functions. `Λ₀`, `Λ₁`, `r` and `M` are
arbitrary upper bounds of the stability sums, the nodal error and the sup norm; quantifying over all upper
bounds is equivalent to using the suprema and avoids a junk `sSup`. -/
theorem lemma_A_4 {d n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (hn : 1 ≤ n) (C : Set (EuclideanSpace ℝ (Fin d))) (hCne : C.Nonempty) (hCc : IsCompact C) (hCv : Convex ℝ C)
    (Q : Submodule ℝ (EuclideanSpace ℝ (Fin d) → ℝ)) (hQ : Q ≤ LinearMap.range (polyEval d))
    (hdim : Module.finrank ℝ Q = n)
    (z : Fin n → EuclideanSpace ℝ (Fin d)) (hz : ∀ i, z i ∈ C) (huni : IsUnisolvent Q z)
    (ℓ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hℓ : IsLagrangeBasis Q z ℓ)
    (F : EuclideanSpace ℝ (Fin d) → G) (hF : ContinuousOn F C) (Ft : Fin n → G) (τ : ℝ) (hτ : 0 ≤ τ)
    (hFt : ∀ i, ‖Ft i - F (z i)‖ ≤ τ) (Λ₀ Λ₁ : ℝ)
    (hΛ₀ : ∀ y ∈ C, ∑ i, |ℓ i y| ≤ Λ₀) (hΛ₁ : ∀ y ∈ C, ∑ i, ‖gradient (ℓ i) y‖ ≤ Λ₁) :
    (∀ (T : EuclideanSpace ℝ (Fin d) → G), IsPolyMap Q T → ∀ r M : ℝ, (∀ i, ‖F (z i) - T (z i)‖ ≤ r) →
      (∀ y ∈ C, ‖T y - F y‖ ≤ M) →
      ∀ y ∈ C, ‖interpolant ℓ Ft y - F y‖ ≤ M + Λ₀ * (r + τ)) ∧
    (CkNear C 1 F → ∀ (T : EuclideanSpace ℝ (Fin d) → G), IsPolyMap Q T → ∀ r M : ℝ,
      (∀ i, ‖F (z i) - T (z i)‖ ≤ r) → (∀ y ∈ C, ‖fderiv ℝ T y - fderiv ℝ F y‖ ≤ M) →
      ∀ y ∈ C, ‖fderiv ℝ (interpolant ℓ Ft) y - fderiv ℝ F y‖ ≤ M + Λ₁ * (r + τ)) ∧
    (∀ (p : ℕ) (β L : ℝ), 0 < β → β ≤ 1 → 0 ≤ L → PolyLE d p ≤ Q → HolderNear C p β L F →
      ∀ y ∈ C, ‖interpolant ℓ Ft y - F y‖ ≤
        (1 + Λ₀) * taylorConst p β * L * Metric.diam C ^ ((p : ℝ) + β) + Λ₀ * τ) := by sorry

end HOTrap
