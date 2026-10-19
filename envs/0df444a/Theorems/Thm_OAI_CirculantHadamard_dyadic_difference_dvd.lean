-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_dyadic_difference_dvd
-- name    : OAI.CirculantHadamard.dyadic_difference_dvd
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:27:43.721809+00:00
-- url     : https://prove2.me/theorems/3a470ee2-84c0-443e-b34e-4f3e61183393
-- title:
--   Dyadic divisibility of opposite coefficient differences
-- statement:
--   Let $k,t\in\mathbb N$, $u$ odd, and $T\in\mathbb Z[\mathbb Z/2^{k+1}]$ with
--   $$
--   T\,T^{*}=2^{2t}u^2 .
--   $$
--
--   Then for every $j\in\{0,\dots,2^k-1\}$, $2^t$ divides $T(j)-T(j+2^k)$. Here $T^{*}(a)=T(-a)$ is the index reversal in the integer cyclic group ring, and an integer $c$ on the right of a norm equation stands for the scalar $c\,e_0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/OrderCyclotomicDivisibility.lean#L52-L112

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

open OAI OAI.CirculantHadamard
universe uA
open Polynomial
open scoped BigOperators

theorem OAI.CirculantHadamard.dyadic_difference_dvd (k t u : ℕ)
    (T : CyclicRing.Elem ℤ (2 ^ (k + 1))) (hu : Odd u)
    (hnorm : T * CyclicRing.ringStar T =
      CyclicRing.scalar (2 ^ (k + 1)) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    ∀ j : ZMod (2 ^ k), (2 : ℤ) ^ t ∣
      T.coeff (j.val : ZMod (2 ^ (k + 1))) -
        T.coeff ((j.val + 2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by sorry
