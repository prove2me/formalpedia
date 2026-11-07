-- Prove2me | Theorems.Thm_GaussMixHH_theorem_1_gap
-- name    : GaussMixHH.theorem_1_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:57.946802+00:00
-- url     : https://prove2.me/theorems/be44b9d0-987b-43f9-9243-e4f2e3567946
-- title:
--   Proof of Theorem 1, p.29 — under either (EP) promise, $\rho_z$ is $(R/2,R)$-gapped with near mass $0$, resp. $D(\mu)$
-- statement:
--   Let $0<\varepsilon_{dist}$, $2\varepsilon_{dist}<\Delta_{\min}$, $R=\varepsilon_{dist}$, $z\in\mathbb R^n$, and let $D$ be a purely atomic center distribution on $\mathbb R^n$ whose atoms are pairwise at distance at least $\Delta_{\min}$. Let $\rho_z$ be the law of $\|\mu-z\|$, $\mu\sim D$.
--
--   1. *(Soundness promise.)* If every center is at distance more than $\varepsilon_{dist}$ from $z$, then $\rho_z$ is $(R/2,R)$-gapped with $\operatorname{near-mass}_R(\rho_z)=0$.
--   2. *(Completeness promise.)* If a center $\mu$ satisfies $\|\mu-z\|\le\varepsilon_{dist}/2$, then $\rho_z$ is $(R/2,R)$-gapped with $\operatorname{near-mass}_R(\rho_z)=D(\mu)$.
--
--   This reduces (EP) to near-mass estimation (Theorem 20) with $R=\varepsilon_{dist}$.
--
--   Differences from the source:
--   - reading: Supp, the set of centers, and D(μ) → the positive-weight atoms of D (D purely atomic on them), D(μ) = D{μ}; reason: the model's discrete D; this makes the promises as weak as possible
--   - encoding: "no center μ ∈ Supp lies within εdist of z" → ∀ μ ∈ Supp D, εdist < ‖μ − z‖; reason: "within" is ≤
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 1, p.29 (PDF p.31); (EP), p.4

import Mathlib
import Definitions.Def_GaussMixHH_CenterModel
import Definitions.Def_GaussMixHH_Gapped

open MeasureTheory

namespace GaussMixHH

/-- **Proof of Theorem 1, gap reduction** (under either promise of (EP) the radial distribution is
`(R/2, R)`-gapped with `R = εdist`, with near mass `0`, resp. `D(μ)`).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 1, pp.28–29
(PDF pp.30–31); the promises are those of (EP), p.4.

"Under the soundness promise in (EP), every center is at distance at least R from z, so the radial
distribution is (R/2, R)-gapped with near mass zero. … Under the completeness promise in (EP), there
is a center μ with ∥μ − z∥ ≤ R/2. Every other center μ′ satisfies
∥μ′ − z∥ ≥ ∆min − ∥μ − z∥ ≥ ∆min − εdist/2 > εdist. The radial distribution is therefore again
(R/2, R)-gapped, now with near mass D(μ)."

**Formalization Note.** The deterministic part of the reduction, with `R = εdist > 0` and
`εdist < ∆min/2`, for a purely atomic `∆min`-separated center distribution (`Supp D` = its
positive-weight atoms, possibly infinite). The soundness promise is "no center within `εdist` of
`z`"; the completeness promise is a center `μ ∈ Supp D` with `∥μ − z∥ ≤ εdist/2`; `D(μ) = D{μ}`. -/
theorem theorem_1_gap (n : ℕ) (εdist Δmin : ℝ) (D : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure D] (z : EuclideanSpace ℝ (Fin n)) (hε : 0 < εdist)
    (hΔ : 2 * εdist < Δmin) (hD : IsSeparatedAtomic Δmin D) :
    ((∀ μ ∈ Supp D, εdist < dist μ z) →
      IsGapped εdist (radialLaw D z) ∧ nearMass εdist (radialLaw D z) = 0) ∧
    (∀ μ ∈ Supp D, dist μ z ≤ εdist / 2 →
      IsGapped εdist (radialLaw D z) ∧ nearMass εdist (radialLaw D z) = (D {μ}).toReal) := by sorry

end GaussMixHH
