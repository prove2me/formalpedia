-- Prove2me | Theorems.Thm_HOTrap_corollary_A_8
-- name    : HOTrap.corollary_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:48:17.152383+00:00
-- url     : https://prove2.me/theorems/d40d4fb4-952e-4721-ab9d-43c5dd8ef15a
-- title:
--   Corollary A.8 — reconstruction from gradient data
-- statement:
--   Let $p\ge1$, $\nu=p+\beta$, let $S$, $c$, $\rho$ be as in §A.2, and suppose $f\in C^{p,\beta}(L)$ on a neighbourhood of $S$. There is a nonadaptively chosen set of $\binom{d+p-1}{p-1}$ nodes in $S$, including $c$, such that supplied gradients with $\|\tilde g_i-\nabla f(z_i)\|_2\le\tau$ determine $P\in\Pi^d_p$ with $P(c)=0$, $\nabla P(c)=\tilde g_c$ and
--   $$
--   \|P-f+f(c)\|_{\infty,S}\le B_0,\qquad\|\nabla P-\nabla f\|_{\infty,S}\le B_1,
--   $$
--   where, with $\Lambda_0,\Lambda_1$ the stability constants of the degree-$(p-1)$ interpolation at these nodes, for $p\ge2$
--   $$
--   B_0:=2a_{p-1,\beta}L\rho^\nu+\rho\Lambda_0\tau,\qquad B_1:=(2a_{p-1,\beta}+a_{p-2,\beta})L\rho^{\nu-1}+\big(\Lambda_0+\tfrac\rho2\Lambda_1\big)\tau,
--   $$
--   and for $p=1$, $B_0:=a_{1,\beta}L\rho^{1+\beta}+\rho\tau$, $B_1:=L\rho^\beta+\tau$, with $\Lambda_0=1$, $\Lambda_1=0$. Moreover, for all $x,y\in S$,
--   $$
--   |P(y)-P(x)-f(y)+f(x)|\le\min\{2B_0,\,B_1\|y-x\|_2\},
--   $$
--   and $2B_0$ can be replaced by $B_0$ when $x=c$. If $L=\tau=0$, then $P=f-f(c)$ on $S$.
--
--   This is the terminal model of the gradient-only algorithm; no function values are required.
--
--   **Formalization Note** $P$ is the integral of Lemma A.7 at $x=c$ of the interpolant of the supplied gradients in the Lagrange basis of $\Pi^d_{p-1}$ at the nodes, so $\Lambda_0,\Lambda_1$ belong to the construction. The sentence on exact gradients is the case $\tau=0$.
--
--   Differences from the source:
--   - encoding: "on a neighborhood of S" → an open set U containing S; reason: the standard meaning of the phrase
--   - encoding: sup norms and the stability constants Λ₀, Λ₁ → pointwise bounds and arbitrary upper bounds of the same quantities; reason: a bound for every upper bound is equivalent to the bound at the supremum, and avoids a junk real sSup
--   - encoding: ρ := max over y in S of ∥y − c∥₂ → ρ with IsGreatest of the image of S under y ↦ ∥y − c∥; reason: the maximum exists because S is compact, and IsGreatest pins it
--   - encoding: supplied gradients determine P → P is lineIntegralModel of the interpolant of the supplied gradients, based at c; reason: this is the construction of the proof, including P(c + v) = ⟨g̃_c, v⟩ for p = 1
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Corollary A.8, Eqs. (68), (69), p.62, with the standing block of §A.2, p.56

import Mathlib
import Definitions.Def_HOTrap_HolderNear
import Definitions.Def_HOTrap_taylorConst
import Definitions.Def_HOTrap_PolyLE
import Definitions.Def_HOTrap_IsUnisolvent
import Definitions.Def_HOTrap_IsLagrangeBasis
import Definitions.Def_HOTrap_interpolant
import Definitions.Def_HOTrap_lineIntegralModel
import Definitions.Def_HOTrap_GradModelBounds

namespace HOTrap

/-- **Corollary A.8 (reconstruction from gradient data).** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Corollary A.8, Eqs. (68), (69), p.62, under the
standing block of §A.2, p.56. Suppose `f ∈ C^{p,β}(L)` near `S`. There is a nonadaptively chosen set of
`(d+p−1 choose p−1)` nodes in `S`, including `c`, such that supplied gradients with `∥g̃ᵢ − ∇f(zᵢ)∥₂ ≤ τ` determine
`P ∈ Π^d_p` with `P(c) = 0`, `∇P(c) = g̃_c`, and (68), (69) hold. Here `Λ₀, Λ₁` are the stability constants of the
degree-`(p−1)` interpolation at these nodes. For `p ≥ 2`, `B₀ := 2a_{p−1,β}Lρ^ν + ρΛ₀τ` and
`B₁ := (2a_{p−1,β} + a_{p−2,β})Lρ^{ν−1} + (Λ₀ + (ρ/2)Λ₁)τ`. For `p = 1`, `B₀ := a_{1,β}Lρ^{1+β} + ρτ` and
`B₁ := Lρ^β + τ`, with `Λ₀ = 1` and `Λ₁ = 0`. If `L = τ = 0`, then `P = f − f(c)` on `S`.

**Formalization Note** `P` is tied to the construction: it is the integral of Lemma A.7 at `x = c` of the
interpolant `W = ∑ₓ g̃ₓ ℓₓ` of the supplied gradients, with `ℓ` the Lagrange basis of `Π^d_{p−1}` at the nodes. For
`p = 1` this is `P(c + v) = ⟨g̃_c, v⟩`, as in the paper's proof. `Λ₀, Λ₁` are arbitrary upper bounds of that basis's
stability sums. The nodes and the basis come before `f`, `L`, `τ` and the data. -/
theorem corollary_A_8 {d p : ℕ} (hp : 1 ≤ p) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSc : IsCompact S) (hSv : Convex ℝ S) (c : EuclideanSpace ℝ (Fin d)) (hc : c ∈ interior S)
    (ρ : ℝ) (hρ : IsGreatest ((fun y => ‖y - c‖) '' S) ρ) (ν : ℝ) (hν : ν = (p : ℝ) + β) :
    ∃ (X : Finset (EuclideanSpace ℝ (Fin d))) (ℓ : X → EuclideanSpace ℝ (Fin d) → ℝ) (hcX : c ∈ X),
      ↑X ⊆ S ∧ X.card = (d + p - 1).choose (p - 1) ∧
      IsUnisolvent (PolyLE d (p - 1)) (Subtype.val : X → EuclideanSpace ℝ (Fin d)) ∧
      IsLagrangeBasis (PolyLE d (p - 1)) (Subtype.val : X → EuclideanSpace ℝ (Fin d)) ℓ ∧
      (p = 1 → (∀ x y, ℓ x y = 1) ∧
        ∀ y, ∑ x, |ℓ x y| = 1 ∧ ∑ x, ‖gradient (ℓ x) y‖ = 0) ∧
      ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (L τ : ℝ) (gt : X → EuclideanSpace ℝ (Fin d)), 0 ≤ L → 0 ≤ τ → HolderNear S p β L f →
        (∀ x : X, ‖gt x - gradient f x‖ ≤ τ) →
        lineIntegralModel (interpolant ℓ gt) c ∈ PolyLE d p ∧
        lineIntegralModel (interpolant ℓ gt) c c = 0 ∧
        gradient (lineIntegralModel (interpolant ℓ gt) c) c = gt ⟨c, hcX⟩ ∧
        (2 ≤ p → ∀ Λ₀ Λ₁ : ℝ, (∀ y ∈ S, ∑ x, |ℓ x y| ≤ Λ₀) →
          (∀ y ∈ S, ∑ x, ‖gradient (ℓ x) y‖ ≤ Λ₁) →
          GradModelBounds S c f (lineIntegralModel (interpolant ℓ gt) c)
            (2 * taylorConst (p - 1) β * L * ρ ^ ν + ρ * Λ₀ * τ)
            ((2 * taylorConst (p - 1) β + taylorConst (p - 2) β) * L * ρ ^ (ν - 1) +
              (Λ₀ + ρ / 2 * Λ₁) * τ)) ∧
        (p = 1 → GradModelBounds S c f (lineIntegralModel (interpolant ℓ gt) c)
          (taylorConst 1 β * L * ρ ^ (1 + β) + ρ * τ) (L * ρ ^ β + τ)) ∧
        (L = 0 → τ = 0 → ∀ y ∈ S, lineIntegralModel (interpolant ℓ gt) c y = f y - f c) := by sorry

end HOTrap
