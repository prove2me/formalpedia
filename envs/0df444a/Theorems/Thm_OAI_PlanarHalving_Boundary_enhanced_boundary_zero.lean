-- Prove2me | Theorems.Thm_OAI_PlanarHalving_Boundary_enhanced_boundary_zero
-- name    : OAI.PlanarHalving.Boundary.enhanced_boundary_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:51:02.416544+00:00
-- url     : https://prove2.me/theorems/219cf2d7-de5c-4b96-b278-c8d7c939442a
-- title:
--   A vertex measure of dimension 32/17 carries no limiting edge activity (OpenAI planar halving lines)
-- statement:
--   This is a technical step of OpenAI's proof that the planar halving-line bound $O(n^{4/3})$ can be improved by a power (*A power saving for planar halving lines*). All named objects are from the definitions bundle `OAIQWPHL000` of this split and the published bundle `Def_HalvingLines`.
--
--   **Setting.** As in the published statement `OAI.PlanarHalving.RankLimits.Converges.positive_part`: configurations $F_n$ (generic point sets with sweep systems of $R$ batches of distance $a$) converge to limiting measures $L$ on `Labels`, the rank labels of points (`Converges F L`), and `L.edgeWindow K` is the limiting edge measure of the window $K$. For a linear automorphism $E$, a centre $o$ and a scale $r$, `physical E o r` is the normalization $p \mapsto r\,E^{-1}(p - o)$ of the plane, and `measures F ψ` are the vertex, window-vertex and window-edge measures of $F$ on `Space` = labels $\times$ a compact cube, where each point carries its label and its normalized position `encode (ψ p)` (`decode` recovers it). `old L` lists the corresponding limiting measures on labels.
--
--   **Statement.** Assume `Converges F L` with sweep embeddings, $R_n \to \infty$, the crossing coefficient $4608\,a^2 n^4/(Ra^2)^3$ bounded by $C \ge 0$, and $13824\, n^3/(Ra^2)^3 \to 0$. Let $K$ be a window, and for each $n$ let $E_n$ be a linear automorphism with $E_n(1,0) = \alpha(1, l)$ and $E_n(0,1) = \beta(1,u)$ for some $\alpha, \beta > 0$ and $l < u$ such that all slopes of the window $K$ of $F_n$ lie in $[l, u]$; let $o_n$ be centres and $r_n > 0$ scales. Suppose that the measures `measures (F n) (physical (E n) (o n) (r n))` converge to finite measures $M_i$ whose label projections are the limits `old L i`. Let $G$ be a measurable set of labels such that
--   - every point of the support of $M_{\text{point}}$ with label in $G$ has normalized position in the closed unit disk, faithfully encoded;
--   - the normalized vertex measure on $G$ has dimension at least $32/17$: every closed disk of radius $t > 0$ has mass at most $D\,t^{32/17}$, for a constant $D \ge 0$.
--
--   Then `L.edgeWindow K G` $= 0$: the limiting edge activity of $K$ on $G$ vanishes.
--
--   In the paper this is the argument of Section 7: in the normalized Euclidean plane "a disk of radius $r$ has mass $O(r^{32/17})$, and hence a thin strip of width $r$ has mass $O(r^{15/17})$", the active vertices of a narrow angular window lie in three such strips or are accounted for by boundary tokens (Lemma 7.1, Lemma 7.2), and summing over windows gives $\lambda_{K_0}(G) \le CM^{-4/3} + C_G M(\delta^{1/12} + \delta^{3/68})$, which tends to zero.
--
--   Lean: `OAI.PlanarHalving.Boundary.enhanced_boundary_zero`, OpenAI's lemma of that name. The carver publishes it as an intermediate statement so that each proof fits the platform's verifier.
-- source:
--   OpenAI, A power saving for planar halving lines, OpenAI Math Release, September 25, 2026, Section 7 (Lemmas 7.1, 7.2 and the packing contradiction), https://github.com/openai/math (result family 183; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/HalvingLines/ActivityRetention.lean (declaration OAI.PlanarHalving.Boundary.enhanced_boundary_zero)

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

namespace PlanarHalving.Boundary
open Set Filter Metric MeasureTheory Batches TimeWindows RankLimits Enhancement Spatial
open scoped Topology unitInterval NNReal ENNReal Classical

lemma enhanced_boundary_zero {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (emb : ∀ n, (F n).SweepEmbedding)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (K : Window) (E : ℕ → Point ≃L[ℝ] Point) (o : ℕ → Point) (r : ℕ → ℝ)
    (hr : ∀ n, 0<r n)
    (hframe : ∀ n, ∃ A B l u : ℝ, 0<A ∧ 0<B ∧ l<u ∧
      E n (1,0)=A • (1,l) ∧ E n (0,1)=B • (1,u) ∧
      ∀ i, ((F n).system.timeWindow K).slope i∈Icc l u)
    {M : Index → FiniteMeasure Space}
    (hM : ∀ i, Tendsto (fun n => measures (F n) (physical (E n) (o n) (r n)) i) atTop (𝓝 (M i)))
    (hprojection : ∀ i, (M i).map Prod.fst=old L i)
    (G : Set Labels) (hG : MeasurableSet G)
    (hpos : ∀ z∈Prod.fst ⁻¹' G ∩ (M .point : Measure Space).support,
      ‖decode z.2‖≤1 ∧ encode (decode z.2)=z.2)
    {D : ℝ} (hD : 0≤D)
    (hdisk : ∀ x : Point, ∀ t : ℝ, 0<t →
      (((M .point : Measure Space).restrict (Prod.fst ⁻¹' G ∩ (M .point : Measure Space).support)).map
        (decode ∘ Prod.snd)) (closedBall x t)≤ENNReal.ofReal (D*t^((32:ℝ)/17))) :
    (L.edgeWindow K G:ℝ)=0 := by
  sorry

end PlanarHalving.Boundary

end OAI
end
