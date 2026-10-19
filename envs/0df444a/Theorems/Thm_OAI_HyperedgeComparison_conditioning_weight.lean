-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_conditioning_weight
-- name    : OAI.HyperedgeComparison.conditioning_weight
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:01:27.801384+00:00
-- url     : https://prove2.me/theorems/10fc2eb6-a262-4cb6-bb3f-b750e55feac0
-- title:
--   Weighted conditioning on clusters avoiding a vertex
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. Let $w$ be a weight on sets with $w(U)=0$ whenever $s\in U$. Then for every observable $F$,
--   $$
--   \mathbb E\bigl[w(\mathcal C_D(S))\,F(\mathcal C_D(s))\bigr]=\mathbb E\bigl[w(\mathcal C_D(S))\,m_{D\cup\mathcal C_D(S)}(F)\bigr].
--   $$
--
--   The weight $w$ allows summing over all possible clusters of $S$ at once.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L591-L618

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison

open OAI OAI.HyperedgeComparison
universe uE uI uV
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
variable {V : Type uV} {E : Type uE}
variable [Fintype E]

theorem OAI.HyperedgeComparison.conditioning_weight [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (D S : Set V)
    (w : Set V → ℝ) (F : Set V → ℝ) (hw : ∀ U, s ∈ U → w U = 0) :
    (∫ ω, w (clusters H ω D S) * F (cluster H ω D s) ∂law p) =
      ∫ ω, w (clusters H ω D S) *
        meanAfterDelete H p s (D ∪ clusters H ω D S) F ∂law p := by sorry
