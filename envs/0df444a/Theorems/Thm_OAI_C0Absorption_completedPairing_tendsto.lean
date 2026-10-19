-- Prove2me | Theorems.Thm_OAI_C0Absorption_completedPairing_tendsto
-- name    : OAI.C0Absorption.completedPairing_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T21:56:43.523437+00:00
-- url     : https://prove2.me/theorems/6f5e22a1-1a04-498d-b52e-6d0ea13aee10
-- title:
--   Pointwise limits of uniformly bounded tests pass to the completion
-- statement:
--   Let $Z$ be the test space: the completion of the molecules on a metric space $S$ under the selected norm $\|m\|^2=\sum_nq_n(m)^2$. Each coordinate $q_n$ is a weighted list seminorm for a class $L_{j(n)}$ of test functions, and every bounded test $f$ extends to a functional $\langle f,\cdot\rangle$ on $Z$. Let $f_n$ be test functions with $|\langle f_n,m\rangle|\le K\|m\|$ for all molecules $m$, converging pointwise to $g$. Then $g$ satisfies the same bound, and for every $z\in Z$,
--   $$
--   \langle f_n,z\rangle\longrightarrow\langle g,z\rangle .
--   $$
--
--   Weak-type limits of tests act continuously on the whole space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Pairings.lean#L121-L143

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem OAI.C0Absorption.completedPairing_tendsto (f : ℕ → S → ℝ) (g : S → ℝ) (K : ℝ≥0)
    (hbound : ∀ n (m : PreSpace L o), |pairing S (f n) m| ≤ K * ‖m‖)
    (hpoint : ∀ s, Filter.Tendsto (fun n => f n s) Filter.atTop (nhds (g s))) :
    (∀ m : PreSpace L o, |pairing S g m| ≤ K * ‖m‖) ∧
    ∀ z : TestSpace L o,
      Filter.Tendsto (fun n => completedPairing L o (f n) z) Filter.atTop
        (nhds (completedPairing L o g z)) := by sorry
