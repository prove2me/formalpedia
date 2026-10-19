-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_rowCirculant_gram_apply
-- name    : OAI.CirculantHadamard.rowCirculant_gram_apply
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:12:03.975467+00:00
-- url     : https://prove2.me/theorems/78523f2b-7779-4aef-ae00-8f6d953a6a5b
-- title:
--   Gram entries of a circulant matrix are autocorrelations
-- statement:
--   Let $n>0$, let $R$ be a commutative ring, and let $h:\mathbb Z/n\to R$ with row circulant $C(h)_{ij}=h(j-i)$. Then for all $i,a\in\mathbb Z/n$,
--   $$
--   \bigl(C(h)\,C(h)^{\mathsf T}\bigr)_{ia}=\sum_{j\in\mathbb Z/n}h(j)\,h\bigl(j-(a-i)\bigr).
--   $$
--
--   So the $(i,a)$ entry of the Gram matrix depends only on $a-i$ and equals the cyclic autocorrelation of $h$ at that shift.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/MatrixBridge.lean#L27-L42

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge

open OAI OAI.CirculantHadamard
universe uR
open scoped BigOperators
variable {n : ℕ}

theorem OAI.CirculantHadamard.rowCirculant_gram_apply [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) (i a : Fin n) :
    (rowCirculant h * (rowCirculant h).transpose) i a =
      ∑ j, h j * h (j - (a - i)) := by sorry
