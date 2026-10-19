-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_weaklyNull_of_finsupp_bound
-- name    : OAI.RecursivePotentials.weaklyNull_of_finsupp_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:11:06.749988+00:00
-- url     : https://prove2.me/theorems/bcfd0ef6-1195-4b32-8fb6-13399c7bb84d
-- title:
--   An $\ell^2$-bounded linear map sends unit vectors to a weakly null sequence
-- statement:
--   Let $E$ be a real normed space and let $c_{00}$ be the real vector space of finitely supported sequences $a:\mathbb{N}\to\mathbb{R}$; write $e_k\in c_{00}$ for the sequence equal to $1$ at $k$ and $0$ elsewhere. A sequence $(d_k)_{k\in\mathbb{N}}$ in $E$ is *weakly null* if $f(d_k)\to0$ as $k\to\infty$ for every continuous linear functional $f:E\to\mathbb{R}$.
--
--   **Theorem.** Let $L:c_{00}\to E$ be a linear map and $C\ge0$ a constant such that
--
--   $$\|L a\|\le C\Bigl(\sum_{k\in\operatorname{supp}a}a_k^2\Bigr)^{1/2}\quad\text{for all }a\in c_{00}.$$
--
--   Then the sequence $(L e_k)_{k\in\mathbb{N}}$ is weakly null in $E$: $f(Le_k)\to0$ for every continuous linear functional $f$ on $E$.
--
--   This is the standard fact that an upper $\ell^2$ estimate forces weak nullity. It is used to show that basis vectors at distinct children of a node in a tree space, whose linear combinations obey such an estimate, form weakly null sequences.
--
--   **Formalization Note** $c_{00}$ is `ℕ →₀ ℝ`, $L$ is a linear map `(ℕ →₀ ℝ) →ₗ[ℝ] E` (no continuity is assumed), and $e_k$ is `Finsupp.single k 1`. Weak nullity is the predicate `WeaklyNull`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean#L344-L370

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms

open OAI OAI.RecursivePotentials
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology

theorem OAI.RecursivePotentials.weaklyNull_of_finsupp_bound {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (ℕ →₀ ℝ) →ₗ[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ a, ‖L a‖ ≤ C * Real.sqrt (∑ k ∈ a.support, a k ^ 2)) :
    WeaklyNull (fun k => L (Finsupp.single k 1)) := by sorry
