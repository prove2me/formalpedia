-- Prove2me | Theorems.Thm_GaussMixHH_lemma_18
-- name    : GaussMixHH.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:29.914043+00:00
-- url     : https://prove2.me/theorems/c907d910-67a1-4174-89d5-ba981cbe26f6
-- title:
--   Lemma 18, p.24 — a near-mass difference $\ge\eta$ forces $|G_\nu(-j/R^2)|\ge\eta/(2\cdot3^k)$ for some $h\le j\le k$
-- statement:
--   Let $0<R\le1$ and $0<\eta<1/4$ (the standing assumptions of §4.3). Let $k$ be an odd integer whose majority polynomial $P_k$ satisfies Lemma 17's approximation bounds for $\eta$, and $h=(k+1)/2$. Let $\rho_1,\rho_2$ be $(R/2,R)$-gapped radial probability distributions with
--
--   $$|\operatorname{near-mass}_R(\rho_1)-\operatorname{near-mass}_R(\rho_2)|\ge\eta,$$
--
--   and $\nu=\rho_1-\rho_2$, $\beta=\eta/(2\cdot3^k)$. Then for some $j\in\{h,\dots,k\}$,
--
--   $$|G_\nu(-j/R^2)|\ge\beta .$$
--
--   This converts a difference in near mass into the hypothesis of Lemma 15, at a parameter $T=j/R^2$ that lies within a factor two of $k/R^2$ whichever $j$ occurs.
--
--   Differences from the source:
--   - generalization: k as in Lemma 17 → every odd k whose P_k satisfies Lemma 17's two approximation bounds for η; reason: the proof uses only those bounds and Σ|a_j| ≤ 3^k (true for all k); Lemma 17's k is one such k
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 18, p.24 (PDF p.26); standing assumptions 0 < R ≤ 1, 0 < η < 1/4 of §4.3, p.23

import Mathlib
import Definitions.Def_GaussMixHH_RadialTransform
import Definitions.Def_GaussMixHH_Gapped
import Definitions.Def_GaussMixHH_MajorityPoly

open MeasureTheory Complex

namespace GaussMixHH

/-- **Lemma 18** (Detecting a difference in near mass).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 18, p.24 (PDF p.26), with
`0 < R ≤ 1`, `0 < η < 1/4` fixed at the start of §4.3, p.23.

"Suppose ρ1, ρ2 are (R/2, R)-gapped radial probability distributions and
|near-mass_R(ρ1) − near-mass_R(ρ2)| ≥ η. Let k, h be as in Lemma 17, let ν = ρ1 − ρ2, and set
β = η/(2 · 3^k). Then, for some j ∈ {h, . . . , k}, |G_ν(−j/R²)| ≥ β."

**Formalization Note.** Generalization: `k` is any odd natural number whose `P_k` satisfies
Lemma 17's two approximation bounds for this `η` (`MajorityApprox k η`); Lemma 17's `k` is one of
them. `G_ν = G_{ρ₁} − G_{ρ₂}`. -/
theorem lemma_18 (R η : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) (hη : 0 < η) (hη4 : η < 1 / 4)
    (k : ℕ) (hk : Odd k) (hP : MajorityApprox k η)
    (ρ₁ ρ₂ : Measure ℝ) [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    (h₁ : IsGapped R ρ₁) (h₂ : IsGapped R ρ₂)
    (hgap : η ≤ |nearMass R ρ₁ - nearMass R ρ₂|) :
    ∃ j ∈ Finset.Icc (majorityThreshold k) k,
      η / (2 * 3 ^ k) ≤
        ‖Gfun ρ₁ ((-(j : ℝ) / R ^ 2 : ℝ) : ℂ) - Gfun ρ₂ ((-(j : ℝ) / R ^ 2 : ℝ) : ℂ)‖ := by sorry

end GaussMixHH
