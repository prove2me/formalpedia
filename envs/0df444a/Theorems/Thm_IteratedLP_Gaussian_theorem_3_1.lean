-- Prove2me | Theorems.Thm_IteratedLP_Gaussian_theorem_3_1
-- name    : IteratedLP.Gaussian.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:21:33.69821+00:00
-- url     : https://prove2.me/theorems/c657ec73-23c5-43f0-813f-824a27bb8a30
-- title:
--   Theorem 3.1 — Gaussian min–max comparison: $P(\Phi<c)\le2P(\phi\le c)$, two-sided under convexity–concavity
-- statement:
--   Let $C\subset\mathbb R^n$ and $D\subset\mathbb R^m$ be nonempty compact sets, let $\psi:C\times D\to\mathbb R$ be continuous, and let $G\in\mathbb R^{m\times n}$, $g\in\mathbb R^m$, $h\in\mathbb R^n$ have mutually independent standard Gaussian entries. With the primary and auxiliary values
--   $$\Phi(G)=\min_{w\in C}\max_{u\in D}\{u^\top Gw+\psi(w,u)\},\qquad\phi(g,h)=\min_{w\in C}\max_{u\in D}\{\|w\|g^\top u+\|u\|h^\top w+\psi(w,u)\},$$
--   1. for every $c\in\mathbb R$,
--   $$\mathbb P(\Phi<c)\le2\,\mathbb P(\phi\le c);$$
--   2. if in addition $C$, $D$ are convex and $\psi$ is convex in $w$ and concave in $u$, then for every $v\in\mathbb R$ and $\varepsilon>0$, $\mathbb P(|\Phi-v|>\varepsilon)\le2\,\mathbb P(|\phi-v|\ge\varepsilon)$.
--
--   This is Gordon's comparison in the form of Thrampoulidis, Oymak and Hassibi (CGMT); the paper uses it, through Corollary 3.2, to localize the LP optimizer of each round.
--
--   Differences from the source:
--
--   - encoding: ψ : C × D → ℝ continuous → ψ : ℝⁿ → ℝᵐ → ℝ with ContinuousOn (uncurry ψ) (C ×ˢ D); reason: only the values on C × D enter the statement
--   - encoding: min over C, max over D → real ⨅ over the subtype C of ⨆ over the subtype D (minMax); reason: attained for nonempty compact sets and a continuous payoff, so equal to the min and max
--   - encoding: ‖w‖, ‖u‖ Euclidean norms; probabilities of events about Φ and ϕ → eNorm = √(Σ wᵢ²); measures of the events under the joint product law gaussTriple of (G, g, h); reason: Lean's default norm on Fin n → ℝ is the sup norm; the joint law has the stated marginals
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 13, Theorem 3.1 (with the setup (3.1)–(3.2))

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_MinMax

open MeasureTheory ProbabilityTheory

namespace IteratedLP.Gaussian

/-- Theorem 3.1 (Gaussian min–max comparison, p. 13). Let `C ⊂ ℝ^n`, `D ⊂ ℝ^m` be nonempty
compact sets, `ψ` continuous on `C × D`, and `G ∈ ℝ^{m×n}`, `g ∈ ℝ^m`, `h ∈ ℝ^n` with mutually
independent standard Gaussian entries. With `Φ(G) = min_{w∈C} max_{u∈D} {u⊤Gw + ψ(w,u)}` and
`ϕ(g,h) = min_{w∈C} max_{u∈D} {‖w‖g⊤u + ‖u‖h⊤w + ψ(w,u)}`:
for every `c`, `P(Φ < c) ≤ 2 P(ϕ ≤ c)`; and if in addition `C`, `D` are convex and `ψ` is convex
in `w` and concave in `u`, then for every `v` and `ε > 0`,
`P(|Φ - v| > ε) ≤ 2 P(|ϕ - v| ≥ ε)`. -/
theorem theorem_3_1 (m n : ℕ) (C : Set (Fin n → ℝ)) (D : Set (Fin m → ℝ))
    (hC : IsCompact C) (hCne : C.Nonempty) (hD : IsCompact D) (hDne : D.Nonempty)
    (ψ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (hψ : ContinuousOn (Function.uncurry ψ) (C ×ˢ D)) :
    (∀ c : ℝ, gaussTriple m n {ω | minMax C D (primaryPayoff ψ ω.1) < c} ≤
      2 * gaussTriple m n {ω | minMax C D (auxPayoff ψ ω.2.1 ω.2.2) ≤ c}) ∧
    (Convex ℝ C → Convex ℝ D → (∀ u ∈ D, ConvexOn ℝ C (fun w => ψ w u)) →
      (∀ w ∈ C, ConcaveOn ℝ D (fun u => ψ w u)) →
      ∀ v ε : ℝ, 0 < ε →
        gaussTriple m n {ω | ε < |minMax C D (primaryPayoff ψ ω.1) - v|} ≤
          2 * gaussTriple m n {ω | ε ≤ |minMax C D (auxPayoff ψ ω.2.1 ω.2.2) - v|}) := by sorry

end IteratedLP.Gaussian
