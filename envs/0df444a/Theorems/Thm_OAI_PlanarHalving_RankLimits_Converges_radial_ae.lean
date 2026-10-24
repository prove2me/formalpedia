-- Prove2me | Theorems.Thm_OAI_PlanarHalving_RankLimits_Converges_radial_ae
-- name    : OAI.PlanarHalving.RankLimits.Converges.radial_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:51:01.725793+00:00
-- url     : https://prove2.me/theorems/cdae59c8-6ac4-45a6-b942-a382de5196ff
-- title:
--   Almost-everywhere radial comparison of the normalized rank charts (OpenAI planar halving lines)
-- statement:
--   This is a technical step of OpenAI's proof that the planar halving-line bound $O(n^{4/3})$ can be improved by a power (*A power saving for planar halving lines*). All named objects are from the definitions bundle `OAIQWPHL000` of this split and the published bundle `Def_HalvingLines`.
--
--   **Setting.** As in the published statements `OAI.PlanarHalving.RankLimits.Converges.positive_part` and `OAI.PlanarHalving.RankLimits.pointwise_radial`: configurations $F_n$ (generic point sets with sweep systems of $R$ batches of distance $a$) converge to limiting measures $L$ (`Converges F L`) on `Labels`, the rank labels of points; `pairCoordinates true A B z` is the point of the rank square given by the $A$- and $B$-coordinates of a label $z$; `L.conditional z` is the conditional law of the batch time given the label; `RadialCompare f p r C T` is the two-sided comparison of $|f - f(p)|$ on the circles of radii $r/T$ and $r$ about $p$. A `CommonChoice K` is a triple of windows inside $K$ arranged as in the Lean definition, with three associated times `q.time`, and `commonSet L q` is the set of labels whose conditional time law charges all three. `commonDirection` is $(1,0), (1,1), (0,1)$, and `commonChart` composes a linear map $E$ with `rankChart`.
--
--   **Statement.** Assume `Converges F L` with sweep embeddings, $R_n \to \infty$, $a_n n \to \infty$, and the three size conditions on $a$, $n$, $R$ of `positive_part` (bounded crossing coefficient, vanishing sparse term, $n/(Ra) \to 0$). Let $K$ be before $A$ and $B$, $A$ before $B$, all of positive length, and let $G_i$ be the joint limits of the coordinates `extendedRank true A B i` for subwindows $i$ of $K$, each differentiable almost everywhere, which recover every label in the support of `L.points` at continuity points ($z_i = G_i(\text{pairCoordinates}(z))$). Let $\nu$ be a measure on labels, absolutely continuous with respect to the edge measure and the vertex measure, whose image under `pairCoordinates true A B` is absolutely continuous with respect to Lebesgue measure. Let $q$ be a `CommonChoice K` such that for $\nu$-almost every $z$ the conditional time law of $z$ charges $K$ and $z \in$ `commonSet L q`. Let $E_n$ be linear automorphisms with $E_n^{-1}$ carrying the sweep direction of $F_n$ at time `q.time i` onto the line of `commonDirection i`.
--
--   Then for $\nu$-almost every label $z$, the point $p = \text{pairCoordinates}(z)$ lies in $(0,1) \times (-1,0)$, and there is $C_0 > 0$ such that for every $T \ge 1$, for all sufficiently small $r > 0$ and then all sufficiently large $n$, the inverse of `commonChart` $F_n$ $E_n$ satisfies `RadialCompare` at $p$ with radius $r$, constant $C_0$ and ratio $T$.
--
--   In the paper this combines the almost-everywhere differentiability of the coordinatewise monotone rank coordinates (Section 4, Lemmas 4.1–4.3), the independent gradients of Section 4.2, and the noncollapse of Section 5.1 at almost every rank point.
--
--   Lean: `OAI.PlanarHalving.RankLimits.Converges.radial_ae`, OpenAI's lemma of that name. The carver publishes it as an intermediate statement so that each proof fits the platform's verifier.
-- source:
--   OpenAI, A power saving for planar halving lines, OpenAI Math Release, September 25, 2026, Sections 4.2–5.1, https://github.com/openai/math (result family 183; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/HalvingLines/Packing.lean (declaration OAI.PlanarHalving.RankLimits.Converges.radial_ae)

import Mathlib
import Definitions.Def_HalvingLines
import Definitions.Def_OAIQWPHL000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom
open scoped Topology unitInterval

lemma Converges.radial_ae {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (emb : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n:ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    {K A B : Window} (hAB : Before A B) (hKA : Before K A) (hKB : Before K B)
    (hA : ∀ n, 0<length (F n).R A) (hB : ∀ n, 0<length (F n).R B)
    (G : Subwindows K → Point → I)
    (hjoint : ∀ i p, ContinuousAt (G i) p → Tendsto
      (fun q : ℕ × Point => (F q.1).extendedRank true A B i.val q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G i p)))
    (hGaed : ∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x:ℝ)) p)
    (hid : ∀ i z, z∈(L.points:Measure Labels).support →
      ContinuousAt (G i) (pairCoordinates true A B z) → z i.val=G i (pairCoordinates true A B z))
    (ν : Measure Labels) (he : ν≪(L.edge:Measure Labels)) (hp : ν≪(L.points:Measure Labels))
    (hproj : ν.map (pairCoordinates true A B)≪volume)
    (q : CommonChoice K)
    (hpos : ∀ᵐ z ∂ν, L.conditional z (carrier K)≠0 ∧ z∈commonSet L q)
    (E : ℕ → Point ≃L[ℝ] Point)
    (hE : ∀ n i, detPair ((E n).symm (1,(F n).timeSlope (q.time i))) (commonDirection i)=0) :
    ∀ᵐ z ∂ν, pairCoordinates true A B z∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 ∧
      ∃ C₀ : ℝ, 0<C₀ ∧ ∀ T : ℝ, 1≤T → ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
        RadialCompare (commonChart (F n) hAB (hA n) (hB n) (E n)).symm
          (pairCoordinates true A B z) r C₀ T := by
  sorry

end PlanarHalving.RankLimits

end OAI
end
