-- Prove2me | Theorems.Thm_OAI_RuledApproximation_exists_nice_outer_integral
-- name    : OAI.RuledApproximation.exists_nice_outer_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:43:15.299635+00:00
-- url     : https://prove2.me/theorems/15351d2b-7a55-4641-b840-b61ffbdc15e5
-- title:
--   Open outer approximations with null frontier and almost the same weighted integral
-- statement:
--   Let $E$ be a finite-dimensional real normed space and let $\mu$ be a Borel measure on $E$ that is finite on compact sets and s-finite. Let $K\subseteq U\subseteq E$ with $K$ compact and $U$ open, let $F:E\to\mathbb{R}$ be continuous with $F\ge0$, and let $\varepsilon>0$. Then there is a set $S\subseteq E$ such that $S$ is open and bounded, $K\subseteq S\subseteq U$, the frontier $\partial S=\overline S\setminus S^{\circ}$ is $\mu$-null, and
--   $$
--   \int_S F\,d\mu<\int_K F\,d\mu+\varepsilon.
--   $$
--
--   Nothing is assumed about the boundary of $K$. A compact set whose boundary may have positive measure is replaced by a slightly larger open set with $\mu$-null frontier (a Jordan measurable set when $\mu$ is Lebesgue measure), on which lattice Riemann sums converge, at an arbitrarily small cost in the weighted integral.
--
--   **Formalization Note** $\mu$ is the `volume` of an arbitrary `MeasureSpace` structure on $E$ satisfying `BorelSpace`, `IsFiniteMeasureOnCompacts` and `SFinite`; boundedness is `Bornology.IsBounded`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/OuterApproximation.lean#L28-L67

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.exists_nice_outer_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [SFinite (volume : Measure E)]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : E → ℝ} (hF : Continuous F) (hFpos : ∀ x, 0 ≤ F x)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ S : Set E, IsOpen S ∧ Bornology.IsBounded S ∧ K ⊆ S ∧ S ⊆ U ∧
      volume (frontier S) = 0 ∧ (∫ x in S, F x) < (∫ x in K, F x) + eps := by sorry
