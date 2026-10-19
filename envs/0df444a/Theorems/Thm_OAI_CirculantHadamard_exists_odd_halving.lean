-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_exists_odd_halving
-- name    : OAI.CirculantHadamard.exists_odd_halving
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:28:24.650976+00:00
-- url     : https://prove2.me/theorems/894f606d-634d-44c5-a09f-060103202592
-- title:
--   Halving an odd-coefficient dyadic norm equation
-- statement:
--   Let $k\in\mathbb N$, $t\ge2$, $u$ odd, and let $T\in\mathbb Z[\mathbb Z/2^{k+1}]$ have all coefficients odd with
--   $$
--   T\,T^{*}=2^{2t}u^2 .
--   $$
--
--   Then there is $U\in\mathbb Z[\mathbb Z/2^k]$ with all coefficients odd and $U\,U^{*}=2^{2(t-1)}u^2$; explicitly $U(j)=\frac{T(j)+T(j+2^k)}2$. Here $T^{*}(a)=T(-a)$ is the index reversal in the integer cyclic group ring, and an integer $c$ on the right of a norm equation stands for the scalar $c\,e_0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/OrderHalving.lean#L153-L173

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

theorem OAI.CirculantHadamard.exists_odd_halving (k t u : ℕ) (T : Elem ℤ (2 ^ (k + 1)))
    (ht : 2 ≤ t) (hu : Odd u) (hodd : ∀ j, Odd (T.coeff j))
    (hnorm : T * ringStar T =
      scalar (2 ^ (k + 1)) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    ∃ U : Elem ℤ (2 ^ k), (∀ j, Odd (U.coeff j)) ∧
      U * ringStar U = scalar (2 ^ k) ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by sorry
