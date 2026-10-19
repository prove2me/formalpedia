-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_gram_eq_iff_autocorrelation
-- name    : OAI.CirculantHadamard.gram_eq_iff_autocorrelation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:12:30.00193+00:00
-- url     : https://prove2.me/theorems/5b8f325c-819e-468e-ad7a-52bd9c49bb46
-- title:
--   Circulant Gram equation versus vanishing autocorrelations
-- statement:
--   Let $n>0$, $R$ a commutative ring, and $h:\mathbb Z/n\to R$ with row circulant $C(h)_{ij}=h(j-i)$. Then $C(h)\,C(h)^{\mathsf T}=n\,I$ holds if and only if for every shift $a\in\mathbb Z/n$
--   $$
--   \sum_{j\in\mathbb Z/n}h(j)\,h(j-a)=\begin{cases}n,&a=0,\\0,&a\ne0.\end{cases}
--   $$
--
--   Thus a circulant matrix is Hadamard-orthogonal exactly when its first row has autocorrelation $n$ at shift zero and $0$ at every other shift.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/MatrixBridge.lean#L44-L63

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge

open OAI OAI.CirculantHadamard
universe uR
open scoped BigOperators
variable {n : ℕ}

theorem OAI.CirculantHadamard.gram_eq_iff_autocorrelation [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) :
    rowCirculant h * (rowCirculant h).transpose =
        (n : R) • (1 : Matrix (Fin n) (Fin n) R) ↔
      ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : R) else 0 := by sorry
