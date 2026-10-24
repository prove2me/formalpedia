-- Prove2me | Theorems.Thm_OAI_PlanarHalving_RankLimits_pointwise_radial
-- name    : OAI.PlanarHalving.RankLimits.pointwise_radial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:52:38.570107+00:00
-- url     : https://prove2.me/theorems/14918110-20dd-4aff-b957-b27a4deaadb0
-- title:
--   Radial comparison of the normalized rank charts at a point with independent gradients (OpenAI planar halving lines)
-- statement:
--   This is a technical step of OpenAI's proof that the planar halving-line bound $O(n^{4/3})$ can be improved by a power (*A power saving for planar halving lines*). All named objects are from the definitions bundle `OAIQWPHL000` of this split and the published bundle `Def_HalvingLines`.
--
--   **Setting.** A `Configuration` $F$ is a generic point set with a sweep system of $R$ batches (slopes increasing in time, marked $k$-sets separated by lines of those slopes). A `Window` is a dyadic subinterval of the time interval $[0,1]$, and `Subwindows K` are the windows inside $K$. For windows $A$ before $B$, `F.rankChart` is the homeomorphism from the plane onto the open rank square given by the pair of rank coordinates $(r_A, r_B)$ (second coordinate reflected), and `F.extendedRank true A B C` expresses the rank coordinate $r_C$ as a function on that square. `F.timeSlope t` is the sweep slope at time $t$. For $f : \mathbb R^2 \to \mathbb R^2$, `RadialCompare f p h C T` says that for all $u, v$ with $|u - p| = h/T$ and $|v - p| = h$,
--   $$|f(v) - f(p)| \le C\,T\,|f(u) - f(p)| \quad\text{and}\quad T\,|f(u) - f(p)| \le C\,|f(v) - f(p)|.$$
--
--   **Statement.** Let $F_n$ be configurations with $R_n \to \infty$, and $K, A, B$ windows with $A$ before $B$ and $K$ before both, of positive length in every $F_n$. Let $G_i$ ($i$ a subwindow of $K$) be the joint limits of the coordinates `extendedRank true A B i` at their continuity points, each differentiable almost everywhere. Let $p \in (0,1) \times (-1,0)$ be a point where every $G_i$ is differentiable. Let $\mu$ be a measure on $[0,1]$ without atoms, with $\mu(K) > 0$, such that every subwindow $J$ of $K$ with $\mu(J) > 0$ contains two subwindows $i, j$ for which $v \mapsto (DG_i(p)v, DG_j(p)v)$ is injective. Let $t_1 < t_2 < t_3$ be interior times of $K$ with $\mu$-positive gaps, let $v_1, v_2, v_3$ be pairwise transverse directions, and let $L_n$ be linear automorphisms of the plane carrying the sweep direction $(1, \text{timeSlope}(t_i))$ of $F_n$ onto the line of $v_i$ for each $i$.
--
--   Then there is $C_0 > 0$ such that for every $T \ge 1$, for all sufficiently small $h > 0$ and then all sufficiently large $n$, the map $x \mapsto L_n(\text{rankChart}_n^{-1}(x))$ satisfies `RadialCompare` at $p$ with scale $h$, constant $C_0$ and ratio $T$.
--
--   In the paper this is Section 5.1: three transverse families of sweep lines with three transverse limiting directions, normalized linearly, satisfy the hypotheses of Lemma 5.1 (three-foliation compactness), which "prevents collapse after a suitable linear normalization". The order of limits (fixed small rank scale $h$ first, then $n$ large) is the paper's.
--
--   Lean: `OAI.PlanarHalving.RankLimits.pointwise_radial`, OpenAI's lemma of that name. The carver publishes it as an intermediate statement so that each proof fits the platform's verifier.
-- source:
--   OpenAI, A power saving for planar halving lines, OpenAI Math Release, September 25, 2026, Section 5.1 (application of Lemma 5.1 to the rank coordinates), https://github.com/openai/math (result family 183; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/HalvingLines/Noncollapse.lean (declaration OAI.PlanarHalving.RankLimits.pointwise_radial)

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
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma pointwise_radial (F : ℕ → Configuration) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {K A B : Window} (hAB : Before A B) (hKA : Before K A) (hKB : Before K B)
    (hA : ∀ n, 0 < length (F n).R A) (hB : ∀ n, 0 < length (F n).R B)
    (G : Subwindows K → Point → I)
    (hjoint : ∀ i p, ContinuousAt (G i) p → Tendsto
      (fun q : ℕ × Point => (F q.1).extendedRank true A B i.val q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G i p)))
    (hGaed : ∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    {p : Point} (hp : p∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hd : ∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    (μ : Measure I) [NullSingletonClass μ] (hpos : μ (carrier K)≠0)
    (hind : ∀ J : Subwindows K, μ (carrier J.val) ≠ 0 →
      ∃ i j : Subwindows K, carrier i.val ⊆ carrier J.val ∧
        carrier j.val ⊆ carrier J.val ∧
        Function.Injective (fun v : Point =>
          ((fderiv ℝ (fun x => (G i x : ℝ)) p) v,(fderiv ℝ (fun x => (G j x : ℝ)) p) v)))
    (t : Fin 3 → I) (ht : ∀ i, t i∈Ioo (lower K) (upper K))
    (htgap : ∀ i j, i<j → μ (Ioo (t i) (t j))≠0)
    (L : ℕ → Point ≃L[ℝ] Point) (v : Fin 3 → Point)
    (hv : ∀ i j, i≠j → detPair (v i) (v j)≠0)
    (hL : ∀ n i, detPair (L n (1,(F n).timeSlope (t i))) (v i)=0) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      RadialCompare (fun x => L n (((F n).rankChart hAB (hA n) (hB n)).symm x)) p h C₀ T := by
  sorry

end PlanarHalving.RankLimits

end OAI
end
