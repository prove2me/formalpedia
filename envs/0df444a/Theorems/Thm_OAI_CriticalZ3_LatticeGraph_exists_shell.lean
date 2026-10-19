-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_exists_shell
-- name    : OAI.CriticalZ3.LatticeGraph.exists_shell
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:28:02.704075+00:00
-- url     : https://prove2.me/theorems/b894ac9b-dd5a-448f-be82-3c86b6c4dfed
-- title:
--   Some shell around a box is crossed through many entrants
-- statement:
--   Work with bond or site percolation on a finite lattice graph $G\subseteq\mathbb Z^3$ under a product law $\mathbb P_p$; "$o\leadsto T$" means that $o$ is connected in $G$ to a vertex of $T$. Boxes $C$ have bits (bonds or sites), exterior vertices adjacent to them, and entry bits. Let $o$ lie outside the expansion of a box $B$ by $R$, and suppose the parameters of all entry bits of the expansions $B+j$, $a\le j<R$, equal $q\le p_0<1$. Then for every $L$ some $j\in[a,R)$ satisfies
--   $$
--   \mathbb P_p\bigl(o\leadsto B\ \text{and}\ |\mathrm{entrants}(B+j)|<L\bigr)\le\frac1{(1-p_0)^L(R-a)} .
--   $$
--
--   Hence in some shell the exploration typically produces many entrants.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ShellProbability.lean#L83-L130

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem OAI.CriticalZ3.LatticeGraph.exists_shell (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (B : Box) (o : G.Node) (q : Set.Icc (0 : ℝ) 1) {p₀ : ℝ}
    (hq : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1) (L a R : ℕ) (haR : a < R)
    (ho : ¬(B.expand R).Contains o.1)
    (hp : ∀ j ∈ Finset.Ico a R, ∀ y, (B.expand j).Exterior y →
      p ((B.expand j).entryBit m y) = q) :
    ∃ j ∈ Finset.Ico a R, (ProductCylinder.law p).real
      {ω | G.Meets m ω o {x | B.Contains x} ∧ (G.entrants m (B.expand j) ω o).card < L} ≤
      1/((1-p₀)^L*(R-a : ℕ)) := by sorry
