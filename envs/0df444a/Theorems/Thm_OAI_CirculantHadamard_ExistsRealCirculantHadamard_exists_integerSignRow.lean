-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_ExistsRealCirculantHadamard_exists_integerSignRow
-- name    : OAI.CirculantHadamard.ExistsRealCirculantHadamard.exists_integerSignRow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:13:00.636218+00:00
-- url     : https://prove2.me/theorems/0063b101-3238-404a-a0c5-f5c9dd10807e
-- title:
--   A real circulant Hadamard matrix yields an integer sign row
-- statement:
--   Let $n>0$. If there is a real $n\times n$ matrix $H$ with entries $\pm1$, $HH^{\mathsf T}=nI$, and $H_{ij}=h(j-i)$ for some $h$ on $\mathbb Z/n$, then there is an integer row $z:\mathbb Z/n\to\{1,-1\}$ whose row circulant satisfies, over the integers,
--   $$
--   C(z)\,C(z)^{\mathsf T}=n\,I .
--   $$
--
--   The real problem is therefore equivalent to a statement about integer sign rows, with no approximation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/MatrixBridge.lean#L110-L133

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge

open OAI OAI.CirculantHadamard
universe uR
open scoped BigOperators
variable {n : ℕ}

theorem OAI.CirculantHadamard.ExistsRealCirculantHadamard.exists_integerSignRow [NeZero n]
    (hH : ExistsRealCirculantHadamard n) : ∃ h : Fin n → ℤ, IsIntegerSignRow h := by sorry
