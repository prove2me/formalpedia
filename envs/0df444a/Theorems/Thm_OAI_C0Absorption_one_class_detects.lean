-- Prove2me | Theorems.Thm_OAI_C0Absorption_one_class_detects
-- name    : OAI.C0Absorption.one_class_detects
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T21:58:51.447742+00:00
-- url     : https://prove2.me/theorems/6a4cf2c0-ac97-415f-99f0-eac71e4e28e2
-- title:
--   A single test class detects a seminormalized sequence with bounded signed sums
-- statement:
--   Let $Z$ be the test space: the completion of the molecules on a metric space $S$ under the selected norm $\|m\|^2=\sum_nq_n(m)^2$. Each coordinate $q_n$ is a weighted list seminorm for a class $L_{j(n)}$ of test functions, and every bounded test $f$ extends to a functional $\langle f,\cdot\rangle$ on $Z$. Let $(m_i)$ in $Z$ satisfy $\|m_i\|\ge r>0$ and have bounded signed sums, $\|\sum_{i<n}\pm m_i\|\le M$. Then there are a class index $h$, a constant $\delta>0$, a subsequence $(m_{\varphi(i)})$ and test functions $f_i\in L_h$ with
--   $$
--   \bigl|\langle f_i,m_{\varphi(i)}\rangle\bigr|\ge\delta\qquad\text{for all }i .
--   $$
--
--   A copy of the $c_0$ basis would be seen uniformly by one class of tests.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Pairings.lean#L273-L294

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
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem OAI.C0Absorption.one_class_detects (m : ℕ → TestSpace L o) (M r : ℝ) (hr : 0 < r)
    (hlower : ∀ i, r ≤ ‖m i‖)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    ∃ h : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : ℕ → S → ℝ, ∀ i, f i ∈ L h ∧ δ ≤ |completedPairing L o (f i) (m (φ i))| := by sorry
