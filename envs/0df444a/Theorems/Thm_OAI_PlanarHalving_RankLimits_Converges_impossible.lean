-- Prove2me | Theorems.Thm_OAI_PlanarHalving_RankLimits_Converges_impossible
-- name    : OAI.PlanarHalving.RankLimits.Converges.impossible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:51:07.292249+00:00
-- url     : https://prove2.me/theorems/44de631d-aada-49a7-bdf5-710eaf4116f2
-- title:
--   No convergent sequence of batch systems nearly attains the crossing bound (OpenAI planar halving lines)
-- statement:
--   This is the limiting contradiction at the heart of OpenAI's proof that the planar halving-line bound $O(n^{4/3})$ can be improved by a power (*A power saving for planar halving lines*). All named objects are from the definitions bundle `OAIQWPHL000` of this split.
--
--   **Setting.** A `Configuration` $F$ is a set of $n$ generic points with a sweep system: $R+1$ increasing slopes and, at each, a marked set of $k$ points separated from the others by a line of that slope, consecutive marked sets differing in exactly $a$ points. `SweepEmbedding` says that the marked sets are states of the rank-$k$ sweep of the point set, at increasing positions. Every point of the plane gets a label in `Labels`, its rank coordinates for all dyadic time windows, and `Converges F L` says that the vertex, edge-time and crossing measures of the configurations $F_n$, as finite measures on labels, converge weakly to those of the limiting data $L$.
--
--   **Statement.** There are no configurations $F_n$ and limiting data $L$ such that `Converges F L`, every $F_n$ has a sweep embedding, $R_n \to \infty$, $a_n n \to \infty$, and
--   $$\frac{4608\, a^2 n^4}{(R a^2)^3} \le C \ \text{ for all } n, \qquad \frac{13824\, n^3}{(R a^2)^3} \to 0, \qquad \frac{n}{R a} \to 0.$$
--   (The conclusion is `False`.)
--
--   The first condition says the batches nearly attain the crossing bound $R \lesssim (n/a)^{4/3}$ of Section 2. In the paper this is the contradiction of Sections 3–7: "The finite reductions show that a failure produces a sequence of consecutive distance-$a$ batches with $N/a \to \infty$ and $R \asymp (N/a)^{4/3}$. We will derive a contradiction from such a sequence." It yields the uniform little-o packing estimate (Theorem 2.1).
--
--   Lean: `OAI.PlanarHalving.RankLimits.Converges.impossible`, OpenAI's lemma of that name. The carver publishes it as an intermediate statement so that each proof fits the platform's verifier.
-- source:
--   OpenAI, A power saving for planar halving lines, OpenAI Math Release, September 25, 2026, Sections 3–7 (the packing contradiction behind Theorem 2.1), https://github.com/openai/math (result family 183; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/HalvingLines/Packing.lean (declaration OAI.PlanarHalving.RankLimits.Converges.impossible)

import Mathlib
import Definitions.Def_OAIQWPHL000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom Spatial Enhancement Boundary
open scoped Topology unitInterval

lemma Converges.impossible {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (emb : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n:ℝ)/((F n).R*(F n).a)) atTop (𝓝 0)) : False := by
  sorry

end PlanarHalving.RankLimits

end OAI
end
