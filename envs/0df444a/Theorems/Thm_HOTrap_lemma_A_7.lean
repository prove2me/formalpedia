-- Prove2me | Theorems.Thm_HOTrap_lemma_A_7
-- name    : HOTrap.lemma_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:56.68364+00:00
-- url     : https://prove2.me/theorems/574ea82a-42d2-43f5-ae27-702e16edb53d
-- title:
--   Lemma A.7 — scalar reconstruction from vector fields
-- statement:
--   Let $p\ge1$, let $S\subset\mathbb R^d$ be compact and convex with nonempty interior, let $x\in S$ and $\rho_x=\max_{y\in S}\|y-x\|_2$. Suppose $f$ is $C^1$ on a neighbourhood of $S$ and $W\in(\Pi^d_{p-1})^d$, and define
--   $$
--   P(x+v):=\int_0^1\langle W(x+tv),v\rangle\,dt.
--   $$
--   Then $P\in\Pi^d_p$, $P(x)=0$ and $\nabla P(x)=W(x)$. If $\|W-\nabla f\|_{\infty,S}\le\eta_0$, then $\|P-f+f(x)\|_{\infty,S}\le\rho_x\eta_0$. If additionally $f$ is $C^2$ near $S$ and $\|DW-\nabla^2f\|_{\infty,S}\le\eta_1$, then
--   $$
--   \|\nabla P-\nabla f\|_{\infty,S}\le\eta_0+\tfrac12\rho_x\eta_1.
--   $$
--
--   A vector polynomial need not be a gradient; this lemma gives the scalar model needed for offline minimization, without further queries.
--
--   Differences from the source:
--   - encoding: "on a neighborhood of S" → an open set U containing S; reason: the standard meaning of the phrase
--   - encoding: P defined at the point x + v → P defined at y, with v = y − x; reason: a change of variable
--   - encoding: ρₓ := max over y in S of ∥y − x∥₂ → ρₓ with IsGreatest of the image of S under y ↦ ∥y − x∥; reason: the maximum exists because S is compact, and IsGreatest pins it
--   - encoding: sup norms over S → pointwise bounds on S by η₀ and η₁; reason: a bound by an arbitrary η is what the sup-norm hypothesis says
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Lemma A.7, p.61, with the standing block of §A.2, p.56

import Mathlib
import Definitions.Def_HOTrap_CkNear
import Definitions.Def_HOTrap_PolyLE
import Definitions.Def_HOTrap_lineIntegralModel

namespace HOTrap

/-- **Lemma A.7 (scalar reconstruction from vector fields).** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Lemma A.7, p.61, under the standing block
of §A.2, p.56 (`p ≥ 1`, `S` compact and convex with nonempty interior). Let `x ∈ S`,
`ρₓ := max_{y∈S} ∥y − x∥₂`, let `f` be `C¹` near `S` and `W ∈ (Π^d_{p−1})^d`, and put
`P(x + v) := ∫₀¹ ⟨W(x + tv), v⟩ dt`. Then `P ∈ Π^d_p`, `P(x) = 0` and `∇P(x) = W(x)`. If `∥W − ∇f∥_{∞,S} ≤ η₀`
then `∥P − f + f(x)∥_{∞,S} ≤ ρₓη₀`. If moreover `f` is `C²` near `S` and `∥DW − ∇²f∥_{∞,S} ≤ η₁`, then
`∥∇P − ∇f∥_{∞,S} ≤ η₀ + (1/2)ρₓη₁`.

**Formalization Note** `∇²f` is `fderiv ℝ (gradient f)`, and `DW − ∇²f` carries the operator norm. The paper's last
sentence, that the construction uses only the coefficients of `W`, is structural: `lineIntegralModel W x`
is a function of `W` and `x` alone. -/
theorem lemma_A_7 {d p : ℕ} (hp : 1 ≤ p) (S : Set (EuclideanSpace ℝ (Fin d))) (hSc : IsCompact S) (hSv : Convex ℝ S)
    (hSi : (interior S).Nonempty) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ S) (ρx : ℝ)
    (hρ : IsGreatest ((fun y => ‖y - x‖) '' S) ρx) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : CkNear S 1 f)
    (W : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hW : ∀ i, (fun y => W y i) ∈ PolyLE d (p - 1)) :
    lineIntegralModel W x ∈ PolyLE d p ∧ lineIntegralModel W x x = 0 ∧
    gradient (lineIntegralModel W x) x = W x ∧
    ∀ η₀ : ℝ, (∀ y ∈ S, ‖W y - gradient f y‖ ≤ η₀) →
      (∀ y ∈ S, |lineIntegralModel W x y - f y + f x| ≤ ρx * η₀) ∧
      (CkNear S 2 f → ∀ η₁ : ℝ,
        (∀ y ∈ S, ‖fderiv ℝ W y - fderiv ℝ (gradient f) y‖ ≤ η₁) →
        ∀ y ∈ S, ‖gradient (lineIntegralModel W x) y - gradient f y‖ ≤ η₀ + 1 / 2 * ρx * η₁) := by sorry

end HOTrap
