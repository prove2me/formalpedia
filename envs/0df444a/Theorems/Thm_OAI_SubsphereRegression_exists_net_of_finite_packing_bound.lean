-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_exists_net_of_finite_packing_bound
-- name    : OAI.SubsphereRegression.exists_net_of_finite_packing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:05:46.676281+00:00
-- url     : https://prove2.me/theorems/eab0986e-90ce-4510-91bd-757dc1747d86
-- title:
--   A bounded packing number yields a separated finite net
-- statement:
--   Let $(E,\operatorname{dist})$ be a pseudometric space, $A\subseteq E$ a set, $r\ge0$ a real number and $N$ a natural number. Call a finite set $s\subseteq E$ *strictly $r$-separated* if $\operatorname{dist}(x,y)>r$ for all distinct $x,y\in s$. Assume that every finite strictly $r$-separated subset of $A$ has at most $N$ elements. Then there is a finite strictly $r$-separated set $s\subseteq A$ which is an $r$-net of $A$:
--   $$\operatorname{dist}(x,y)>r\ \ (x,y\in s,\ x\ne y)\qquad\text{and}\qquad\forall x\in A\ \ \exists y\in s:\ \operatorname{dist}(x,y)\le r.$$
--   In particular $s$ has at most $N$ points.
--
--   This turns a packing bound into a covering: once the size of separated subsets of $A$ is controlled (for example by a volume argument), $A$ is covered by at most $N$ closed balls of radius $r$ centred at points of $A$ itself. It is used to produce explicit nets of the unit ball in finite-dimensional normed spaces.
--
--   **Formalization Note** Finite sets are `Finset E` and the hypotheses are stated pointwise for their elements. In a pseudometric space distinct points may be at distance $0$; the statement and proof are unaffected.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Geometry.lean#L181-L224

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
variable {E : Type*} [PseudoMetricSpace E]

theorem OAI.SubsphereRegression.exists_net_of_finite_packing_bound (A : Set E) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hcard : ∀ s : Finset E, (∀ x ∈ s, x ∈ A) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) → s.card ≤ N) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) ∧
      ∀ x ∈ A, ∃ y ∈ s, dist x y ≤ r := by sorry
