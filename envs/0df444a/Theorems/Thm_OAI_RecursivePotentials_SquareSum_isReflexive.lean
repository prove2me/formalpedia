-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_SquareSum_isReflexive
-- name    : OAI.RecursivePotentials.SquareSum.isReflexive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:19:23.167325+00:00
-- url     : https://prove2.me/theorems/f44b06c4-9102-4df1-88c9-17cf205616f9
-- title:
--   The $\ell^2$-sum of reflexive normed spaces is reflexive
-- statement:
--   For a real normed space $E$, write $E^{*}$ for the space of continuous linear functionals on $E$ and $J_E:E\to E^{**}$ for the canonical map $J_E(x)(f)=f(x)$. The space $E$ is *reflexive* if $J_E$ is surjective (no completeness is assumed in this definition).
--
--   Let $(E_i)_{i\in\iota}$ be a family of real normed spaces indexed by an arbitrary set $\iota$. Their *$\ell^2$-sum* $\ell^2(E)$ is the space of families $x=(x_i)_{i\in\iota}$ with $x_i\in E_i$ and $\sum_i\|x_i\|^2<\infty$, normed by $\|x\|=\bigl(\sum_i\|x_i\|^2\bigr)^{1/2}$.
--
--   **Theorem.** If every $E_i$ is reflexive, then $\ell^2(E)$ is reflexive:
--
--   $$\bigl(\forall i\in\iota:\ J_{E_i}(E_i)=E_i^{**}\bigr)\ \Longrightarrow\ J_{\ell^2(E)}\bigl(\ell^2(E)\bigr)=\ell^2(E)^{**}.$$
--
--   In the development this yields reflexivity of the joined tree space and of its zero-root subspace, which are isomorphic to $\ell^2$-sums of reflexive component spaces (up to a one-dimensional summand), and of the variable-exponent $\ell^2$-sum.
--
--   **Formalization Note** $\ell^2(E)$ is `SquareSum.Space E` $=$ `lp E 2`; reflexivity is `IsReflexive`, the surjectivity of `NormedSpace.inclusionInDoubleDual ℝ`. The index type carries a `DecidableEq` instance, which is no mathematical restriction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/JoinedGeometry.lean#L334-L359

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.SquareSum
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

theorem OAI.RecursivePotentials.SquareSum.isReflexive (hE : ∀ i, IsReflexive (E i)) : IsReflexive (Space E) := by sorry
