-- Prove2me | Theorems.Thm_NatureSLT_Margin_mercer_theorem
-- name    : NatureSLT.Margin.mercer_theorem
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:07.106181+00:00
-- url     : https://prove2.me/theorems/715e97d0-0940-4b17-93a5-7b652c9632b7
-- title:
--   Theorem 5.3 (Mercer) — K(u, v) = Σ a_k ψ_k(u)ψ_k(v) with a_k > 0 iff ∫∫ K(u, v) g(u) g(v) du dv > 0 for all g ≠ 0 in L₂
-- statement:
--   Let $d \ge 1$ and let $U \subseteq \mathbb R^d$ be a measurable set of positive Lebesgue measure, and let $K(u, v)$ be a symmetric function on $U \times U$ belonging to $L_2(U \times U)$. **Theorem 5.3 (Mercer)** states that, for $K$ to have an expansion
--
--   $$K(u, v) = \sum_{k=1}^{\infty} a_k\, \psi_k(u)\, \psi_k(v) \tag{5.24}$$
--
--   with positive coefficients $a_k > 0$ (i.e., for $K(u, v)$ to describe an inner product in some feature space), it is necessary and sufficient that the condition
--
--   $$\int\!\!\int K(u, v)\, g(u)\, g(v)\, du\, dv > 0$$
--
--   be valid for all $g \neq 0$ for which $\int g^2(u)\, du < \infty$.
--
--   In the support vector machine this condition decides which functions $K(x_i, x)$ may replace the inner product $(z_i \cdot z)$ in feature space in (5.17) and (5.20).
--
--   **Formalization Note** The expansion is read in the Hilbert–Schmidt sense: the $\psi_k$ (indexed from $0$) are orthonormal in $L_2(U)$, and the partial sums $\sum_{k < N} a_k \psi_k(u)\psi_k(v)$ converge to $K$ in $L_2(U \times U)$. The measure $du$ is Lebesgue measure restricted to $U$, and $d \ge 1$ (for $d = 0$ Lebesgue measure is a point mass, $L_2(U)$ is one-dimensional, and no infinite orthonormal system exists); "$g \neq 0$" means that $g$ is not zero almost everywhere on $U$. The double integral is taken with respect to the product measure on $U \times U$. Symmetry is required pointwise on $U \times U$. As printed, the "necessary" direction is believed false (F1 in the mission's findings): an expansion with positive coefficients over an orthonormal system that is not complete gives $\int\!\!\int K g g = 0$ for a nonzero $g$ orthogonal to all $\psi_k$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 140–141, Theorem 5.3

import Mathlib
open MeasureTheory Filter Topology

namespace NatureSLT.Margin

/-- **Theorem 5.3 (Mercer)** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed.,
pp. 140–141): to guarantee that the symmetric function `K(u, v)` from `L₂` has an expansion
`K(u, v) = ∑_{k=1}^∞ a_k ψ_k(u) ψ_k(v)` (5.24) with positive coefficients `a_k > 0`, it is necessary
and sufficient that the condition `∫∫ K(u, v) g(u) g(v) du dv > 0` be valid for all `g ≠ 0` for
which `∫ g²(u) du < ∞`.

The variables `u, v` range over a measurable set `U ⊆ ℝᵈ` (`d ≥ 1`) of positive Lebesgue measure, `du` is
Lebesgue measure on `U`, and `L₂` is `L²(U)` (for `K`: `L²(U × U)`). `K` is symmetric on `U × U`.
The expansion is read in the standard (Hilbert–Schmidt) sense: `ψ₁, ψ₂, …` (indexed from `0`)
are orthonormal in `L²(U)` and the partial sums converge to `K` in `L²(U × U)`.
"`g ≠ 0`" means `g` is not zero almost everywhere on `U`. -/
theorem mercer_theorem {d : ℕ} (hd : 0 < d) (U : Set (EuclideanSpace ℝ (Fin d)))
    (hU : MeasurableSet U)
    (hU0 : 0 < volume U) (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (hsymm : ∀ u ∈ U, ∀ v ∈ U, K u v = K v u)
    (hK : MemLp (Function.uncurry K) 2 ((volume.restrict U).prod (volume.restrict U))) :
    (∃ (a : ℕ → ℝ) (ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ),
        (∀ k, 0 < a k) ∧ (∀ k, MemLp (ψ k) 2 (volume.restrict U)) ∧
        (∀ j k, ∫ u in U, ψ j u * ψ k u = if j = k then 1 else 0) ∧
        Tendsto (fun N : ℕ => eLpNorm (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
            K p.1 p.2 - ∑ k ∈ Finset.range N, a k * ψ k p.1 * ψ k p.2) 2
              ((volume.restrict U).prod (volume.restrict U))) atTop (𝓝 0)) ↔
      ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, MemLp g 2 (volume.restrict U) →
        ¬ (g =ᵐ[volume.restrict U] 0) →
        0 < ∫ p, K p.1 p.2 * g p.1 * g p.2 ∂((volume.restrict U).prod (volume.restrict U)) := by sorry

end NatureSLT.Margin
