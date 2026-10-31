-- Prove2me | Theorems.Thm_LeGallBrownianMap_theorem_2_4
-- name    : LeGallBrownianMap.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:48.298849+00:00
-- url     : https://prove2.me/theorems/db091c62-31cc-4454-9a1b-55b7d3c9b380
-- title:
--   Theorem 2.4 — geodesics to $x_*$ are simple geodesics, hence $D^*$-geodesics
-- statement:
--   In the setting of Theorem 2.3, almost surely: every geodesic in $(m_\infty,D)$ from an arbitrary point $x$ of $m_\infty$ to $x_*=p(s_*)$ is a simple geodesic $\Gamma_s$, $\Gamma_s(r)=p(\varphi_s(r))$, $0\le r\le D(x,x_*)$, for some $s$ with $p(s)=x$; and therefore it is also a geodesic in $(m_\infty,D^*)$: $D^*(\gamma(t),\gamma(t'))=t'-t$ for $0\le t\le t'\le D(x,x_*)$.
--
--   A geodesic from $x$ to $y$ is a path $(\gamma(t))_{0\le t\le d(x,y)}$ with $\gamma(0)=x$, $\gamma(d(x,y))=y$ and $d(\gamma(t),\gamma(t'))=t'-t$. The theorem, a reformulation of results of [16], is the main tool for comparing $D$ with $D^*$ along geodesics.
--
--   **Formalization Note** Points of $m_\infty$ are represented by times in $[0,1]$, equal points meaning $D=0$, and a path is a function of representatives.
--
--   Differences from the source:
--   - encoding: in the setting of Theorem 2.3 ((e, Z, D) a subsequential limit of (5)) → hypothesis IsBDGSubseqLimit p φ e Z D P for a strictly increasing φ; reason: a property of the joint law of (e, Z, D), exactly the setting used in §§3–7
--   - encoding: points of m∞ and paths in m∞; equality of points → representative times in [0,1] and functions γ : ℝ → [0,1]; equality as D = 0; reason: p is onto and D(s,t) = 0 iff p(s) = p(t)
--   - reading: the statement about the random space (m∞, D) → almost surely, simultaneously for all points and all geodesics; reason: a statement about a random metric space
--   - encoding: x∗ = p(s∗), s∗ the a.s. unique minimizer of Z → s∗ = sStar Z, a chosen minimizer; reason: the minimizer is a.s. unique
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, Theorem 2.4, p.19 (definitions pp.18–19)

import Mathlib
import Definitions.Def_LeGallBrownianMap_IsBDGSubseqLimit
import Definitions.Def_LeGallBrownianMap_dStar
import Definitions.Def_LeGallBrownianMap_sStar
import Definitions.Def_LeGallBrownianMap_simpleGeodesicTime

open MeasureTheory

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, Theorem 2.4,
p.19: "All geodesics in (m∞, D) from an arbitrary vertex of m∞ to x∗ are simple geodesics, and
therefore also geodesics in (m∞, D∗)." In the setting of Theorem 2.3; `x∗ = p(s∗)`; a geodesic
from `x` to `y` is "a path (ω(t), 0 ≤ t ≤ d(x, y)) such that ω(0) = x, ω(d(x, y)) = y and
d(ω(t), ω(t′)) = t′ − t for every 0 ≤ t ≤ t′ ≤ d(x, y)" (p.18); simple geodesics are the paths
`Γ_s(r) = p(ϕ_s(r))`, `0 ≤ r ≤ D(s, s∗)` (pp.18–19).

For `p ≥ 2` and every subsequential limit `(e, Z, D)` of (5): almost surely, for every point
`x = p(x₀)` of `m∞` and every geodesic `γ` in `(m∞, D)` from `x` to `x∗` (of length
`L = D(x₀, s∗)`):
1. `γ` is a simple geodesic: there is `s` with `p(s) = x` and `γ(r) = Γ_s(r)` for all
   `r ∈ [0, L]`;
2. `γ` is a geodesic in `(m∞, D∗)`: `D∗(γ(t), γ(t')) = t' − t` for `0 ≤ t ≤ t' ≤ L`.

**Formalization Note.** Points of `m∞ = [0,1]/≈` are represented by times in `[0,1]`, two times
representing the same point iff `D = 0` between them; a path in `m∞` is a function `γ : ℝ → [0,1]`
of representatives (only its values on `[0, L]` matter), and equalities of points are `D = 0`.
`D∗` on `m∞` is `D∗` on representatives (p.18). `s∗` is `sStar Z`. "The setting of Theorem 2.3"
is `IsBDGSubseqLimit`. One null set for all `x` and all `γ`. -/
theorem theorem_2_4 (p : ℕ) (hp : 2 ≤ p) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (φ : ℕ → ℕ) (e Z : Ω → unitInterval → ℝ)
    (D : Ω → unitInterval → unitInterval → ℝ) (hlim : IsBDGSubseqLimit p φ e Z D P) :
    ∀ᵐ ω ∂P, ∀ (x₀ : unitInterval) (γ : ℝ → unitInterval),
      D ω (γ 0) x₀ = 0 →
      D ω (γ (D ω x₀ (sStar (Z ω)))) (sStar (Z ω)) = 0 →
      (∀ t t' : ℝ, 0 ≤ t → t ≤ t' → t' ≤ D ω x₀ (sStar (Z ω)) →
        D ω (γ t) (γ t') = t' - t) →
      (∃ s : unitInterval, D ω s x₀ = 0 ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ D ω x₀ (sStar (Z ω)) →
          D ω (γ r) (simpleGeodesicTime (Z ω) s r) = 0) ∧
      (∀ t t' : ℝ, 0 ≤ t → t ≤ t' → t' ≤ D ω x₀ (sStar (Z ω)) →
        dStar (e ω) (Z ω) (γ t) (γ t') = t' - t) := by sorry

end LeGallBrownianMap
