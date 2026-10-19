-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_cyclic_reduction_fiber_card
-- name    : OAI.CirculantHadamard.cyclic_reduction_fiber_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:16:31.048597+00:00
-- url     : https://prove2.me/theorems/9af5b855-7a82-490e-a3e9-6b26f9b17303
-- title:
--   Fibres of reduction between cyclic groups have equal size
-- statement:
--   Let $m,n>0$ with $n=md$. For every $a\in\mathbb Z/m$, the number of $x\in\mathbb Z/n$ reducing to $a$ modulo $m$ is
--   $$
--   \#\{x\in\mathbb Z/n:\ x\bmod m=a\}=d .
--   $$
--
--   Reduction $\mathbb Z/n\to\mathbb Z/m$ is surjective with all fibres of the same size $n/m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/OrderProjection.lean#L29-L52

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection

open OAI OAI.CirculantHadamard
universe uα
open scoped BigOperators

theorem OAI.CirculantHadamard.cyclic_reduction_fiber_card {n m d : ℕ} [NeZero n] [NeZero m]
    (hdiv : m ∣ n) (hn : n = m * d) (a : ZMod m) :
    Fintype.card {x : ZMod n // ZMod.castHom hdiv (ZMod m) x = a} = d := by sorry
