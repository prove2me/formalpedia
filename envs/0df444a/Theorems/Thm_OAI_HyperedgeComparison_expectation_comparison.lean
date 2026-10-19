-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_expectation_comparison
-- name    : OAI.HyperedgeComparison.expectation_comparison
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:09:56.306961+00:00
-- url     : https://prove2.me/theorems/0ebd81d4-3791-428e-b939-3fb75c0cf594
-- title:
--   Comparison of cluster expectations at a new vertex
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on a finite set $V$ with finitely many labels, and $\mathbb P_p$ the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e<1$. $\mathcal C(x)$ denotes the cluster of $x$ and "$x$ meets $T$" means $\mathcal C(x)\cap T\ne\varnothing$. Let $x_0,\dots,x_n$ be distinct vertices and $F\ge0$ an increasing function of sets. If $\mathbb E\,F(\mathcal C(x_j))\ge b$ for all $j<n$, then
--   $$
--   b\,\bigl(1-\mathbb P(\mathcal C(x_n)\cap\{x_0,\dots,x_{n-1}\}=\varnothing)\bigr)\le\mathbb E\,F(\mathcal C(x_n)).
--   $$
--
--   The factor $1-B_{nn}$ is the probability that the new cluster meets one of the earlier vertices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L1393-L1434

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

theorem OAI.HyperedgeComparison.expectation_comparison [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin (n + 1) → V) (hx : Function.Injective x) (F : Set V → ℝ)
    (hF0 : ∀ U, 0 ≤ F U) (hFm : Monotone F) (b : ℝ)
    (hb : ∀ j ≠ Fin.last n, b ≤ expectationVector H p x F j) :
    b * (1 - baseMatrix H p x (Fin.last n) (Fin.last n)) ≤
      expectationVector H p x F (Fin.last n) := by sorry
