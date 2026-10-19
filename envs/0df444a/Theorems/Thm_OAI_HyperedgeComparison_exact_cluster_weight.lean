-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_exact_cluster_weight
-- name    : OAI.HyperedgeComparison.exact_cluster_weight
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:00:59.744152+00:00
-- url     : https://prove2.me/theorems/9c168a0f-a40b-4f1c-b6e6-80e4d7f543d9
-- title:
--   Integrating functions away from the cluster with an independent copy
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. Let $g(\omega,U)$ depend, for each fixed $U$, only on hyperedges disjoint from $U$. Then for every $f$,
--   $$
--   \mathbb E_\omega\bigl[f(\mathcal C^\omega_D(S))\,g(\omega,\mathcal C^\omega_D(S))\bigr]=\mathbb E_\omega\Bigl[f(\mathcal C^\omega_D(S))\ \mathbb E_{\omega'}\bigl[g(\omega',\mathcal C^\omega_D(S))\bigr]\Bigr].
--   $$
--
--   It is the integrated form of the spatial Markov property.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L564-L589

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

theorem OAI.HyperedgeComparison.exact_cluster_weight [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S : Set V) (f : Set V → ℝ)
    (g : (E → Bool) → Set V → ℝ)
    (hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U) :
    (∫ ω, f (clusters H ω D S) * g ω (clusters H ω D S) ∂law p) =
      ∫ ω, f (clusters H ω D S) * (∫ ω', g ω' (clusters H ω D S) ∂law p) ∂law p := by sorry
