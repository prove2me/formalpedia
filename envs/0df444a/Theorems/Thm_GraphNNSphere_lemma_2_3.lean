-- Prove2me | Theorems.Thm_GraphNNSphere_lemma_2_3
-- name    : GraphNNSphere.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:25.503508+00:00
-- url     : https://prove2.me/theorems/704cf850-1d26-4253-b22a-652d4f9e9775
-- title:
--   Lemma 2.3 — improving directions
-- statement:
--   Let $x,y\in S^{d-1}$ with $\delta(x,y)=t\in(0,\pi)$, and let $0<\theta<\pi/2$. Among the queries $q$ with $\delta(q,x)=\theta$, those with $\delta(q,y)<\theta$ form a spherical cap in the $(d-2)$-sphere of directions at $x$, with cosine threshold $h=\cot\theta\tan(t/2)$.
--
--   1. The cap is empty when $h\ge1$.
--   2. When $h<1$, its normalized measure is at most $\sqrt{d-1}\,(1-h^2)^{(d-4)/2}$, and it decreases as $t$ increases.
--   3. For $d\ge5$ and $0\le h<1$, the measure is at least $c_0(d-1)^{-1/2}(1-h^2)^{(d-2)/2}$ for an absolute constant $c_0>0$.
--   4. Consequently, for every fixed $\varepsilon>0$, the measure is $(1-h^2)^{(d-1)/2}e^{O_\varepsilon(\log(d-1))}$ uniformly for $0\le h\le1-\varepsilon$.
--
--   This bounds, for one stored edge, the fraction of query directions for which the edge improves.
--
--   **Formalization Note** The queries at distance $\theta$ from $x$ are written $\cos\theta\,x+\sin\theta\,v$ with $v$ on the unit sphere of $x^\perp$, and $y=\cos t\,x+\sin t\,w$ for a unit vector $w\in x^\perp$.
--
--   Differences from the source:
--   - encoding: the spherical cap with threshold h → the set of improving directions equals {v | h < ⟪v, w⟫} for the unit direction w of y in x^⊥; reason: this is the meaning of a cap with cosine threshold h
--   - reading: "decreases as t increases" → nonincreasing for every d, and strictly decreasing for d ≥ 3, as t ranges over values with h(t₁) < 1 and t₁ < t₂ (for any y₁, y₂ at those distances from x); reason: at d = 2 the sphere of directions has two points and strictness fails
--   - reading: e^{O_ε(log(d−1))} with no range of d → d ≥ 3; reason: at d = 2 the logarithm vanishes while the two sides differ, so the printed form needs d ≥ 3
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.3, p.17

import Mathlib
import Definitions.Def_GraphNNSphere_geo
import Definitions.Def_GraphNNSphere_dirLaw
import Definitions.Def_GraphNNSphere_improvingDirs

open scoped RealInnerProductSpace

namespace GraphNNSphere

/-- Lemma 2.3, improving directions (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the
Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.3, p.17).

**Formalization Note** The queries at distance `θ` from `x` are `cos θ x + sin θ v`, with `v` on the
unit sphere of `x^⊥`. The first clause gives the cap, the emptiness for `h ≥ 1`, and the upper bound,
which the page states with no range of `d` and which holds for every `d`. "Decreases as `t`
increases" is nonincreasing for all `d`, and strict for `d ≥ 3`; at `d = 2` the sphere of directions
has two points and strictness fails. `e^{O_ε(log(d-1))}` is stated for `d ≥ 3`, as at `d = 2` the
logarithm vanishes while the measure and `(1 - h²)^{(d-1)/2}` differ. -/
theorem lemma_2_3 :
    (∀ (d : ℕ) (x y : Sph d) (θ : ℝ), 0 < geo x y → geo x y < Real.pi → 0 < θ →
      θ < Real.pi / 2 →
      let t := geo x y
      let h := Real.cot θ * Real.tan (t / 2)
      (∀ w : DirSphere x,
        (y : EuclideanSpace ℝ (Fin d)) = Real.cos t • (x : EuclideanSpace ℝ (Fin d)) +
          Real.sin t • (((w : ↥(Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))})ᗮ)) :
            EuclideanSpace ℝ (Fin d)) →
        improvingDirs x y θ = {v | h < ⟪(((v : ↥(Submodule.span ℝ
            {(x : EuclideanSpace ℝ (Fin d))})ᗮ)) : EuclideanSpace ℝ (Fin d)),
          (((w : ↥(Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))})ᗮ)) :
            EuclideanSpace ℝ (Fin d))⟫}) ∧
      (1 ≤ h → improvingDirs x y θ = ∅) ∧
      (h < 1 → (dirLaw x (improvingDirs x y θ)).toReal ≤
        Real.sqrt ((d : ℝ) - 1) * (1 - h ^ 2) ^ (((d : ℝ) - 4) / 2))) ∧
    (∀ (d : ℕ) (x y₁ y₂ : Sph d) (θ : ℝ), 0 < geo x y₁ → geo x y₁ < geo x y₂ →
      geo x y₂ < Real.pi → 0 < θ → θ < Real.pi / 2 →
      Real.cot θ * Real.tan (geo x y₁ / 2) < 1 →
      (dirLaw x (improvingDirs x y₂ θ)).toReal ≤ (dirLaw x (improvingDirs x y₁ θ)).toReal ∧
      (3 ≤ d →
        (dirLaw x (improvingDirs x y₂ θ)).toReal < (dirLaw x (improvingDirs x y₁ θ)).toReal)) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (d : ℕ) (x y : Sph d) (θ : ℝ), 5 ≤ d → 0 < geo x y →
      geo x y < Real.pi → 0 < θ → θ < Real.pi / 2 →
      Real.cot θ * Real.tan (geo x y / 2) < 1 →
      c₀ * ((d : ℝ) - 1) ^ (-(1 / 2) : ℝ) *
          (1 - (Real.cot θ * Real.tan (geo x y / 2)) ^ 2) ^ (((d : ℝ) - 2) / 2) ≤
        (dirLaw x (improvingDirs x y θ)).toReal) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (d : ℕ) (x y : Sph d) (θ : ℝ), 3 ≤ d → 0 < geo x y →
      geo x y < Real.pi → 0 < θ → θ < Real.pi / 2 →
      Real.cot θ * Real.tan (geo x y / 2) ≤ 1 - ε →
      |Real.log (dirLaw x (improvingDirs x y θ)).toReal -
          ((d : ℝ) - 1) / 2 * Real.log (1 - (Real.cot θ * Real.tan (geo x y / 2)) ^ 2)| ≤
        C * Real.log ((d : ℝ) - 1)) := by sorry

end GraphNNSphere
