-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_odd_norm_impossible
-- name    : OAI.CirculantHadamard.odd_norm_impossible
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T09:29:44.968485+00:00
-- url     : https://prove2.me/theorems/052c1596-b63c-4b98-90eb-8cc019bbc2b5
-- title:
--   No odd-coefficient dyadic group-ring element has a small norm
-- statement:
--   Let $t\ge1$, $k\ge t+2$, $u$ odd, and let $T\in\mathbb Z[\mathbb Z/2^k]$ have all coefficients odd. Then the norm equation
--   $$
--   T\,T^{*}=2^{2t}u^2
--   $$
--   is impossible.
--
--   Repeated halving lowers both exponents by one until the norm is $4u^2$ on a group of order divisible by $8$, where the coefficients modulo $8$ give a contradiction. Here $T^{*}(a)=T(-a)$ is the index reversal in the integer cyclic group ring, and an integer $c$ on the right of a norm equation stands for the scalar $c\,e_0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/OrderDescent.lean#L21-L55

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving

open OAI OAI.CirculantHadamard
open CyclicRing

theorem OAI.CirculantHadamard.odd_norm_impossible {k t u : ℕ}
    (ht : 1 ≤ t) (hkt : t + 2 ≤ k) (hu : Odd u)
    (T : Elem ℤ (2 ^ k)) (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * ringStar T = scalar (2 ^ k) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    False := by sorry
