-- Prove2me | Theorems.Thm_OAI_PlanarHalving_RankLimits_Converges_positive_part
-- name    : OAI.PlanarHalving.RankLimits.Converges.positive_part
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:51:30.97087+00:00
-- url     : https://prove2.me/theorems/b415d85e-80aa-41b1-b3aa-155765da8209
-- title:
--   A positive part of the limiting edge mass sees crossings and vertices (OpenAI planar halving lines)
-- statement:
--   This is a technical step of OpenAI's proof that the planar halving-line bound $O(n^{4/3})$ can be improved by a power (*A power saving for planar halving lines*). All named objects are from the definitions bundle `OAIQWPHL000` of this split.
--
--   **Setting.** A `Configuration` $F$ is a generic set of $n$ points with a sweep system: $R+1$ increasing slopes and, at each, a marked set of $k$ points separated from the rest by a line of that slope, consecutive marked sets differing in exactly $a$ points (a sequence of $R$ batches of distance $a$). A `Window` is a dyadic subinterval of the time interval $[0,1]$ (`carrier`), `Before A B` says that $A$ ends before $B$ begins, and `SeparatedBefore K H` that $0 < \inf K$, $\sup K < \inf H$ and $\sup H < 1$. Every point of the plane gets a label in `Labels` $= [0,1]^{\text{Window}}$, its rank coordinates for all windows. A `Data` $L$ holds finite measures on labels: the vertex measure `L.points`, the edge-time measure `L.edgeTime` on labels $\times$ times (with label marginal `L.edge` and conditional time law `L.conditional z`), and crossing measures `L.crossings A B`. `Converges F L` says that the corresponding finite measures of the configurations $F_n$ converge weakly to those of $L$, and `SweepEmbedding` that the system's marked sets are states of the rank-$k$ sweep at increasing positions.
--
--   **Statement.** Let $F_n$ be configurations with `Converges F L`, each with a sweep embedding, with $R_n \to \infty$, and with
--   - $4608\, a^2 n^4 / (R a^2)^3 \le C$ for all $n$ (the batches nearly attain the crossing bound);
--   - $13824\, n^3/(R a^2)^3 \to 0$ and $n / (R a) \to 0$.
--
--   Then there are windows $K, H, A, B$ and a measurable set $T$ of labels with:
--   - `SeparatedBefore K H`, $A, B \subseteq H$, and $A$ before $B$;
--   - $T$ of positive `L.edge` measure, and the conditional time law of every $z \in T$ charging both $K$ and $H$;
--   - `L.edge` restricted to $T$ absolutely continuous with respect to the crossing measure `L.crossings A B` and with respect to the vertex measure `L.points`.
--
--   In the paper these are Lemma 3.3 ("Edge mass sees crossings": $\lambda_K \ll \sum_{I,J} \sigma_{IJ}$), the absolute continuity of edge endpoint mass with respect to vertex mass, and the choice of windows in Section 4.2 leading to (4.3).
--
--   Lean: `OAI.PlanarHalving.RankLimits.Converges.positive_part`, OpenAI's theorem of that name. The carver publishes it as an intermediate statement so that each proof fits the platform's verifier.
-- source:
--   OpenAI, A power saving for planar halving lines, OpenAI Math Release, September 25, 2026, Sections 3.3 and 4.2 (Lemma 3.3 and equation (4.3)), https://github.com/openai/math (result family 183; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/HalvingLines/Continuity.lean (declaration OAI.PlanarHalving.RankLimits.Converges.positive_part)

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
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped Topology unitInterval ENNReal

theorem Converges.positive_part {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0)) :
    ∃ (K H A B : Window) (T : Set Labels), SeparatedBefore K H ∧
      carrier A ⊆ carrier H ∧ carrier B ⊆ carrier H ∧ Before A B ∧
      MeasurableSet T ∧ (L.edge : Measure Labels) T ≠ 0 ∧
      (∀ z ∈ T, L.conditional z (carrier K) ≠ 0 ∧ L.conditional z (carrier H) ≠ 0) ∧
      (L.edge : Measure Labels).restrict T ≪ (L.crossings A B : Measure Labels) ∧
      (L.edge : Measure Labels).restrict T ≪ (L.points : Measure Labels) := by
  sorry

end PlanarHalving.RankLimits

end OAI
end
