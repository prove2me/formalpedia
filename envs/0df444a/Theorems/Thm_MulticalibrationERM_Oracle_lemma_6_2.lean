-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_lemma_6_2
-- name    : MulticalibrationERM.Oracle.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:52:54.310816+00:00
-- url     : https://prove2.me/theorems/e3a4e863-96c3-4230-91b8-946035fdc5ca
-- title:
--   Lemma 6.2 — rounding with one seed per cell against a VC class of tests
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $G$ be a class of functions $g:X\times\Lambda\to\{-1,+1\}$ of VC dimension at most $d_G$, $d_G\ge1$; $\varphi:X\times\Lambda\to\mathbb R$ a fixed weight function; $P$ a finite measurable partition of $X$ with $\varphi_R\ge|\varphi(x,v)|$ for $x\in R$, $v\in\Lambda$; $V_\varphi=\sum_{R\in P}\varphi_R^2D_X(R)^2$. Let $Q$ be a randomized predictor on $\Lambda$ and $G_x:\Xi\to\Lambda$ maps with $G_x(\xi)\sim Q_x$ for $\xi\sim\mu_\Xi$; draw independent seeds $\xi_R\sim\mu_\Xi$, one per cell, and set $p(x)=G_x(\xi_{R(x)})$. With probability at least $1-\delta$ over the seeds,
--   $$\sup_{g\in G}\Big|\mathbb E\big[g(X,p(X))\varphi(X,p(X))\big]-\mathbb E\Big[\sum_vQ_X(v)\,g(X,v)\,\varphi(X,v)\Big]\Big|\le C\sqrt{V_\varphi\,(d_G+\log(2/\delta))}.$$
--
--   Differences from the source:
--   - encoding: the partition P of the rounding procedure (singletons of O and further measurable cells) → any finite measurable partition, given by a map cell : X → ι into a finite type; reason: with O = ∅ the procedure's partition is already an arbitrary finite measurable partition; O, the intervals and the support condition do not enter the lemma
--   - encoding: D_X the input marginal of D → any probability measure DX on X; reason: only D_X enters; every probability on X is a marginal
--   - reading: maps G_x with G_x(ξ) ∼ Q_x, a fixed weight φ → (x, ξ) ↦ G_x(ξ) jointly measurable and φ measurable; reason: the expectations over X require measurability; standing measurability assumption
--   - generalization: a class G of VC dimension d_G → any class of VC dimension at most d_G; reason: every class of VC dimension exactly d_G is an instance
--   - encoding: auditors h : X → {−1,+1} → h : X → Bool with value pm (h x) ∈ {1, −1} (true ↦ +1); reason: relabelling of the two values; every auditor is an instance
--   - reading: the standard measurability conditions for suprema over H (p. 12) → every auditor measurable and the class pointwise measurable (a countable subclass whose sequences converge pointwise to every member); reason: the paper names no specific condition; pointwise measurability is the standard one under which the suprema are suprema over a countable class
--   - encoding: probability of the failure event → the measure applied to the failure set, i.e. its outer measure when the set is not measurable; reason: equal to the probability when the event is measurable; an outer-measure bound is never weaker
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 33, Lemma 6.2

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_OEMC

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Lemma 6.2 (p. 33): rounding against a VC class of tests. Let `G` be a class of functions
`g : X × Λ → {−1, +1}` of VC dimension at most `d_G`, `d_G ≥ 1`; `φ : X × Λ → ℝ` a fixed weight
function; `P` a finite measurable partition of `X` (cells `{x | cell x = i}`) with `φ_R ≥ |φ(x, v)|`
for `x ∈ R`; `V_φ = ∑_R φ_R² D_X(R)²`. Let `Q` be a randomized predictor on `Λ`, and
`G_x : Ξ → Λ` maps with `G_x(ξ) ∼ Q_x` for `ξ ∼ μΞ`. With independent seeds `ξ_R ∼ μΞ`, one per
cell, and `p(x) = G_x(ξ_{R(x)})`: with probability at least `1 − δ` over the seeds,
`sup_{g ∈ G} |E[g(X, p(X)) φ(X, p(X))] − E[∑_v Q_X(v) g(X, v) φ(X, v)]|
 ≤ C √(V_φ (d_G + log(2/δ)))`, with `C` absolute. -/
theorem lemma_6_2 :
    ∃ C : ℝ, 0 < C ∧
    ∀ {X : Type} [MeasurableSpace X] (DX : Measure X) [IsProbabilityMeasure DX] (K : ℕ), 1 ≤ K →
    ∀ (G : Set (X × Fin (K + 1) → Bool)) (dG : ℕ), 1 ≤ dG → VC G ≤ dG →
      (∀ g ∈ G, Measurable g) → PointwiseMeasurableClass G →
    ∀ (φ : X × Fin (K + 1) → ℝ), Measurable φ →
    ∀ (Q : X → Fin (K + 1) → ℝ), IsGridPred K Q →
    ∀ {ι : Type} [Fintype ι] (cell : X → ι), (∀ i, MeasurableSet {x | cell x = i}) →
    ∀ (φR : ι → ℝ), (∀ x v, |φ (x, v)| ≤ φR (cell x)) →
    ∀ {Ξ : Type} [MeasurableSpace Ξ] (μΞ : Measure Ξ) [IsProbabilityMeasure μΞ]
      (Gq : X → Ξ → Fin (K + 1)), Measurable (Function.uncurry Gq) →
      (∀ x i, μΞ {ξ | Gq x ξ = i} = ENNReal.ofReal (Q x i)) →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      (Measure.pi fun _ : ι => μΞ)
          {ξ | C * Real.sqrt ((∑ i, φR i ^ 2 * (DX {x | cell x = i}).toReal ^ 2) *
                (dG + Real.log (2 / δ))) <
              ⨆ g : G, |∫ x, pm (g.1 (x, cellRound cell Gq ξ x)) * φ (x, cellRound cell Gq ξ x) ∂DX -
                ∫ x, ∑ v, Q x v * pm (g.1 (x, v)) * φ (x, v) ∂DX|} ≤
        ENNReal.ofReal δ := by sorry

end MulticalibrationERM.Oracle
