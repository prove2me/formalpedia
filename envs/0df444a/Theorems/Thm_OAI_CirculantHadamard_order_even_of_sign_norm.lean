-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_order_even_of_sign_norm
-- name    : OAI.CirculantHadamard.order_even_of_sign_norm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:13:32.87898+00:00
-- url     : https://prove2.me/theorems/05c2ba5e-beff-4160-b909-7f84aaa005bb
-- title:
--   A sign row with norm n forces n to be even
-- statement:
--   Let $n>1$ and let $f\in\mathbb Z[\mathbb Z/n]$ have all coefficients in $\{1,-1\}$. If
--   $$
--   f\,f^{*}=n,
--   $$
--   where $f^{*}(a)=f(-a)$ and $n$ denotes the scalar $n\,e_0$, then $n$ is even.
--
--   The coefficient of $f f^{*}$ at the nonzero shift $1$ is a vanishing sum of $n$ signs, which can only happen for even $n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/OrderSquareEven.lean#L49-L64

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm

open OAI OAI.CirculantHadamard
universe uIota
open scoped BigOperators

theorem OAI.CirculantHadamard.order_even_of_sign_norm {n : ℕ} [NeZero n] (hn : 1 < n)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    Even n := by sorry
