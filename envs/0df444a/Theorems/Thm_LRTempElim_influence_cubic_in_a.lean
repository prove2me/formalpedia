-- Prove2me | Theorems.Thm_LRTempElim_influence_cubic_in_a
-- name    : LRTempElim.influence_cubic_in_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:06.988781+00:00
-- url     : https://prove2.me/theorems/9a4a6428-0f34-4a97-b387-adc8603877f7
-- title:
--   §A.2.3: the influence output at an independent query is a cubic in $a$
-- statement:
--   Let $U,V,E$ be independent standard Gaussians and $B\in\{-1,1\}$ an independent fair sign, $W=(U-a/2,V+a/2)\sim Q_a\otimes P_a$ and $X=Ba/2+E\sim\nu_a$ an independent query. Let $\Psi_a$ be the path influence function with features $\phi=(1,x,x^2)$. There are functions $G_0,\dots,G_3$ of $(U,V,B,E)$, not depending on $a$, with every moment finite under the law of $(U,V,B,E)$, such that for every $a$, $U$, $V$, $E$ and $B\in\{-1,1\}$
--   $$
--   \phi(Ba/2+E)^\top\Psi_a(U-a/2,\,V+a/2)=\sum_{j=0}^{3}a^j\,G_j(U,V,B,E).
--   $$
--   That is, the influence output is a polynomial in $a$ of degree at most three with finite Gaussian coefficient moments.
--
--   Squaring and taking expectations gives the sixth-order upper bound $C_{\mathrm{path}}(a)=O(1+a^6)$ of the goal theorem.
--
--   Differences from the source:
--   - reading: "a polynomial in a of degree at most three with finite Gaussian coefficient moments" → ∑_{j=0}^{3} a^j G_j(U, V, B, E) with G_j free of a and G_j ∈ L^r for every r ∈ ℕ under N(0,1) ⊗ N(0,1) ⊗ ½(δ₋₁ + δ₁) ⊗ N(0,1); reason: "finite moments" read as all moments, the stronger reading
--   - encoding: the influence output at the query X → ϕ(X)⊤Ψ_a(W) with W = (U − a/2, V + a/2) and X = Ba/2 + E, pointwise in (U, V, B, E); reason: the representation of the laws named in the sentence
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §A.2.3, p.20 (pdf p.22)

import Mathlib
import Definitions.Def_LRTempElim_PathEstimator

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace LRTempElim

/-- **The influence output at an independent query is a cubic in a** (§A.2.3). Chen, Wu, Yang,
Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination*, STOC 2027
submission (manuscript of 2026-11-03, sha256 eee65139…), §A.2.3, p.20 (pdf p.22).

"To evaluate the influence output at an independent query `X = Ba/2 + E`, with `B ∈ {−1, 1}`
balanced and `E ∼ N(0, 1)`, multiply the centered coefficients by `(1, X − µ_t, (X − µ_t)²)`. The
result is a polynomial in a of degree at most three with finite Gaussian coefficient moments."

**Formalization Note.** The influence output is `ϕ(X)⊤Ψ_a(W)` with `ϕ = (1, x, x²)`, `Ψ_a` the
influence function (51) (`influence phi3 a`), `W = (U − a/2, V + a/2)` with `U, V` independent
standard Gaussians, and `X = Ba/2 + E` (law `ν_a`). "A polynomial in a of degree at most three" is
`∑_{j=0}^{3} a^j G_j(U, V, B, E)` with coefficients `G_j` that do not depend on `a`, holding for
every `a, U, V, E` and `B ∈ {−1, 1}`. "Finite Gaussian coefficient moments" is read as every
moment: `G_j ∈ L^r` for every `r ∈ ℕ` under `N(0,1) ⊗ N(0,1) ⊗ ½(δ₋₁ + δ₁) ⊗ N(0,1)`, the law of
`(U, V, B, E)`. -/
theorem influence_cubic_in_a :
    let γ : Measure ℝ := gaussianReal 0 1
    let sign : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (-1) + Measure.dirac 1)
    let law : Measure (ℝ × ℝ × ℝ × ℝ) := γ.prod (γ.prod (sign.prod γ))
    ∃ G : Fin 4 → ℝ × ℝ × ℝ × ℝ → ℝ,
      (∀ j : Fin 4, ∀ r : ℕ, MemLp (G j) (r : ℝ≥0∞) law) ∧
      ∀ a U V E B : ℝ, (B = -1 ∨ B = 1) →
        phi3 (B * a / 2 + E) ⬝ᵥ influence phi3 a (U - a / 2, V + a / 2) =
          ∑ j : Fin 4, a ^ (j : ℕ) * G j (U, V, B, E) := by sorry

end LRTempElim
