-- Prove2me | Theorems.Thm_MultiphaseDisj_lemma_2_15
-- name    : MultiphaseDisj.lemma_2_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:14.411581+00:00
-- url     : https://prove2.me/theorems/942d582f-c4cd-44fb-9298-2356d0e78ceb
-- title:
--   Lemma 2.15 — from near-rectangles to rectangles
-- statement:
--   Let $\mathcal S$ be a finite family of sets and $d,\kappa,\delta\ge0$ real numbers. If $\mu$ is a $\delta$-monochromatic $(d,\kappa)$-near-rectangle on $\mathcal S\times\mathcal S$, then the product $\mu_A\otimes\mu_B$ of its marginals is a
--   $$
--   \Big(\delta+\sqrt{(\ln 2/2)\,\kappa}\Big)\text{-monochromatic } d\text{-rectangle}.
--   $$
--
--   Replacing a near-rectangle by the product of its marginals changes it little in total variation (Pinsker's inequality), so it puts little more mass on intersecting pairs; this is how the main proof passes from a correlated distribution to a genuine rectangle.
--
--   **Formalization Note** Mutual information is in bits, so Pinsker's inequality carries the factor $\ln2/2$.
--
--   Differences from the source:
--   - encoding: a finite family S of sets → a finite family of finite subsets of a finite type; reason: same instances
--   - encoding: d, κ, δ ≥ 0 (Definition 2.13) → not assumed; reason: they follow from the hypotheses: a deficit, a mutual information and a probability are nonnegative
--   - encoding: H, I, H∞ and log with base 2 (§2.2) → entropy, mutual information and min-entropy in bits on finite sample spaces with real point masses; reason: same quantities
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Lemma 2.15, p.14

import Mathlib
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Lemma 2.15 (From near-rectangles to rectangles)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Lemma 2.15, p.14). Let `S` be a
finite family of sets and `d, κ, δ ≥ 0`. If `μ` is a `δ`-monochromatic `(d, κ)`-near-rectangle on
`S × S`, then `μ_A ⊗ μ_B` is a `(δ + √((ln 2/2) κ))`-monochromatic `d`-rectangle.

**Formalization Note** Sets are finite subsets of a finite type `α`; mutual information is in
bits (§2.2, "Logarithms are base 2 unless written ln"), and `ln 2` is `Real.log 2`. The standing
`d, κ, δ ≥ 0` of Definition 2.13 are not assumed: they follow from the two hypotheses (a deficit,
a mutual information and a probability are nonnegative). -/
theorem lemma_2_15 {α : Type*} [Fintype α] (S : Finset (Finset α)) (d κ δ : ℝ)
    (μ : Finset α × Finset α → ℝ)
    (hmono : IsMono δ μ) (hnear : IsNearRect S d κ μ) :
    IsRect S d (prodDist (marg1 μ) (marg2 μ)) ∧
      IsMono (δ + Real.sqrt (Real.log 2 / 2 * κ)) (prodDist (marg1 μ) (marg2 μ)) := by sorry

end MultiphaseDisj
