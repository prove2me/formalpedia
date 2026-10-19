-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_zmod_double_cast_eq_iff
-- name    : OAI.CirculantHadamard.zmod_double_cast_eq_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:14:32.655529+00:00
-- url     : https://prove2.me/theorems/f19b1b58-98d1-4c0a-a4a0-aab51413c349
-- title:
--   The two lifts of a residue from Z/m to Z/2m
-- statement:
--   Let $m>0$. For $x\in\mathbb Z/2m$ and $j\in\mathbb Z/m$, writing $\bar j\in\{0,\dots,m-1\}$ for the representative of $j$,
--   $$
--   x\bmod m=j\iff x=\bar j\ \text{ or }\ x=\bar j+m\quad\text{in }\mathbb Z/2m .
--   $$
--
--   Each residue modulo $m$ has exactly the two lifts $\bar j$ and $\bar j+m$ modulo $2m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/ProjectionPairFiber.lean#L15-L43

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection

open OAI OAI.CirculantHadamard

theorem OAI.CirculantHadamard.zmod_double_cast_eq_iff {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (x : ZMod (2 * m)) (j : ZMod m) :
    ZMod.castHom h (ZMod m) x = j ↔
      x = (j.val : ZMod (2 * m)) ∨ x = ((j.val + m : ℕ) : ZMod (2 * m)) := by sorry
