-- Prove2me | Theorems.Thm_HOTrap_proposition_A_5
-- name    : HOTrap.proposition_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:48:58.60825+00:00
-- url     : https://prove2.me/theorems/a68f5802-c99a-426b-b22c-529e6a1c2c8e
-- title:
--   Proposition A.5 — local polynomial reconstruction
-- statement:
--   Let $p\ge1$, let $S\subset\mathbb R^d$ be compact and convex with nonempty interior, let $c\in\mathrm{int}(S)$ and $\rho=\max_{y\in S}\|y-c\|_2$. There is a nonadaptively chosen node set $X_p\subset S$, containing $c$, with $|X_p|=\binom{d+p}p$, such that for $F\in C^{p,\beta}(L)$ on a neighbourhood of $S$, supplied values with $\|\tilde F_i-F(z_i)\|\le\tau$ determine a polynomial map $P$ with components in $\Pi^d_p$, with $P(c)=\tilde F_c$ and
--   $$
--   \|D^j(P-F)\|_{\infty,S}\le\frac32a_{p-j,\beta}L\rho^{p-j+\beta}+\Lambda_j\tau,\qquad j=0,1.
--   $$
--
--   For exponents $\beta_1,\dots,\beta_p\in(0,1]$ the constructions admit nested node sets $X_0=\{c\}\subset X_1\subset\dots\subset X_p$ with $|X_j|=\binom{d+j}j$, and at degree $j\ge1$ the bound uses $(j,\beta_j,L_j)$ whenever $F\in C^{j,\beta_j}(L_j)$, with the stability constants of the degree-$j$ node set. At degree zero, the constant model $P\equiv\tilde F_c$ satisfies $\|P-F\|_{\infty,S}\le L_0\rho^\beta+\tau$ whenever $F\in C^{0,\beta}(L_0)$, with stability constants $\Lambda_0=1$, $\Lambda_1=0$.
--
--   Applied to $F=\nabla f$, this gives the gradient reconstruction of Corollary A.8.
--
--   **Formalization Note** Eq. (58) and its side conditions are packaged in the definition `HOTrap.LocalReconstruction`. The nodes and the basis depend only on $S,c,d,p,\beta$ and precede $F$, $L$, $\tau$.
--
--   Differences from the source:
--   - generalization: F scalar- or vector-valued, with Euclidean output norms → F takes values in any real Banach space G; reason: ℝ and ℝ^m are Banach spaces, so the printed statement is the instance G = ℝ^m
--   - encoding: "on a neighborhood of S" → an open set U containing S; reason: the standard meaning of the phrase
--   - encoding: sup norms and the stability constants Λ₀, Λ₁ → pointwise bounds and arbitrary upper bounds of the same quantities; reason: a bound for every upper bound is equivalent to the bound at the supremum, and avoids a junk real sSup
--   - encoding: ρ := max over y in S of ∥y − c∥₂ → ρ with IsGreatest of the image of S under y ↦ ∥y − c∥; reason: the maximum exists because S is compact, and IsGreatest pins it
--   - encoding: exponents β₁, …, β_p → a sequence b : ℕ → ℝ of which only b 1, …, b p are constrained and read; reason: a finite family as a sequence; values outside 1..p play no role
--   - encoding: supplied values determine a polynomial map P with each component in Π^d_p → P is the interpolant ∑ₓ F̃ₓ ℓₓ in the Lagrange basis ℓ of Π^d_p at X, and IsPolyMap (Π^d_p) P; reason: this is the construction of the proof (p.57); IsPolyMap is "each component in Π^d_p" for G = ℝ or ℝ^m
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Proposition A.5, Eq. (58), p.56, with the standing block of §A.2, p.56

import Mathlib
import Definitions.Def_HOTrap_HolderNear
import Definitions.Def_HOTrap_LocalReconstruction

universe u

namespace HOTrap

/-- **Proposition A.5 (local polynomial reconstruction).** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Proposition A.5, Eq. (58), p.56, under the
standing block of §A.2, p.56: `p ≥ 1`, `S ⊂ ℝ^d` compact and convex with nonempty interior, `c ∈ int(S)` and
`ρ := max_{y∈S} ∥y − c∥₂`. Three statements. (i) There is a nonadaptively chosen node set `X_p ⊂ S` with the
property `LocalReconstruction`, namely Eq. (58). (ii) For exponents `β₁,…,β_p ∈ (0,1]` there are nested node
sets `X₀ = {c} ⊂ X₁ ⊂ ⋯ ⊂ X_p` with the same property at each degree `1 ≤ j ≤ p` for `(j, βⱼ)`, and the degree-zero
basis is the constant one, whose stability constants are `Λ₀ = 1`, `Λ₁ = 0`. (iii) At degree zero, the constant
model `P ≡ F̃_c` satisfies `∥P − F∥_{∞,S} ≤ L₀ρ^β + τ` whenever `F ∈ C^{0,β}(L₀)`.

**Formalization Note** The nodes and basis are quantified before the map, the constant and the data error,
inside `LocalReconstruction`. In (ii) the sequence `b` holds the exponents, and only `b 1,…,b p` are read. `ρ` is a
maximum, which exists because `S` is compact: `IsGreatest` pins it. -/
theorem proposition_A_5 {d p : ℕ} (hp : 1 ≤ p) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSc : IsCompact S) (hSv : Convex ℝ S) (c : EuclideanSpace ℝ (Fin d)) (hc : c ∈ interior S)
    (ρ : ℝ) (hρ : IsGreatest ((fun y => ‖y - c‖) '' S) ρ) :
    (∃ (X : Finset (EuclideanSpace ℝ (Fin d))) (ℓ : X → EuclideanSpace ℝ (Fin d) → ℝ), LocalReconstruction.{u} S c ρ p β X ℓ) ∧
    (∀ b : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ p → 0 < b j ∧ b j ≤ 1) →
      ∃ (X : ℕ → Finset (EuclideanSpace ℝ (Fin d))) (ℓ : ∀ j, X j → EuclideanSpace ℝ (Fin d) → ℝ),
        X 0 = {c} ∧ (∀ j, j < p → X j ⊆ X (j + 1)) ∧
        (∀ x y, ℓ 0 x y = 1) ∧
        (∀ y, ∑ x, |ℓ 0 x y| = 1 ∧ ∑ x, ‖gradient (ℓ 0 x) y‖ = 0) ∧
        ∀ j, 1 ≤ j → j ≤ p → LocalReconstruction.{u} S c ρ j (b j) (X j) (ℓ j)) ∧
    (∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (F : EuclideanSpace ℝ (Fin d) → G) (Fc : G) (L τ : ℝ), 0 ≤ L → 0 ≤ τ → HolderNear S 0 β L F →
      ‖Fc - F c‖ ≤ τ → ∀ y ∈ S, ‖Fc - F y‖ ≤ L * ρ ^ β + τ) := by sorry

end HOTrap
