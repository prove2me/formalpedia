-- Prove2me | Theorems.Thm_OAI_C0Absorption_seminorm_sign_pair
-- name    : OAI.C0Absorption.seminorm_sign_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T21:55:01.040621+00:00
-- url     : https://prove2.me/theorems/a9809f4e-3a18-464c-88ee-756daaedb852
-- title:
--   Flipping one sign controls a single term
-- statement:
--   Let $q$ be a seminorm on a real vector space, $m_1,\dots,m_n$ vectors, $\varepsilon$ a choice of signs, and $\varepsilon'$ the signs with the $i$-th one flipped. Then
--   $$
--   2\,q(m_i)^2\le q\Bigl(\sum_j\varepsilon_jm_j\Bigr)^2+q\Bigl(\sum_j\varepsilon'_jm_j\Bigr)^2 .
--   $$
--
--   Each term of a signed sum is controlled by the two signed sums differing in its sign.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Signs.lean#L118-L134

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset

theorem OAI.C0Absorption.seminorm_sign_pair {X : Type*} [AddCommGroup X] [Module ℝ X]
    (q : Seminorm ℝ X) {n : ℕ} (m : Fin n → X) (ε : Fin n → Bool) (i : Fin n) :
    2 * (q (m i)) ^ 2 ≤
      (q (∑ j, realSign (ε j) • m j)) ^ 2 +
      (q (∑ j, realSign (flipSign i ε j) • m j)) ^ 2 := by sorry
