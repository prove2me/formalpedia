-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_exists_two_adic_square_decomposition_of_eq_sq
-- name    : OAI.CirculantHadamard.exists_two_adic_square_decomposition_of_eq_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:14:01.807988+00:00
-- url     : https://prove2.me/theorems/24612d8b-deb5-4011-81a1-faf36eebcb05
-- title:
--   Two-adic form of an even positive square
-- statement:
--   Let $n=m^2$ with $m>0$, and suppose $n$ is even. Then there are $s\ge1$ and an odd $u>0$ with
--   $$
--   n=2^{2s}u^2 .
--   $$
--
--   So every even positive square is a positive even power of two times an odd square.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/TwoAdicDecomposition.lean#L16-L32

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm

open OAI OAI.CirculantHadamard

theorem OAI.CirculantHadamard.exists_two_adic_square_decomposition_of_eq_sq {n m : ℕ}
    (hm : 0 < m) (hnm : n = m ^ 2) (heven : Even n) :
    ∃ s u : ℕ, 1 ≤ s ∧ 0 < u ∧ Odd u ∧ n = 2 ^ (2 * s) * u ^ 2 := by sorry
