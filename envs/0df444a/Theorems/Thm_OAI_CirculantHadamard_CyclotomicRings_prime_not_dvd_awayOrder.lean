-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_CyclotomicRings_prime_not_dvd_awayOrder
-- name    : OAI.CirculantHadamard.CyclotomicRings.prime_not_dvd_awayOrder
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:35:19.674092+00:00
-- url     : https://prove2.me/theorems/27a70746-f450-4db4-9736-41d1e92c6c90
-- title:
--   The omitted prime does not divide the away order
-- statement:
--   Let $u$ be odd and $p$ a prime divisor of $u$. Then
--   $$
--   p\nmid4\prod_{\substack{q\mid u\ \text{prime}\\ q\ne p}}q .
--   $$
--
--   The single generator $i\prod_{q\ne p}\rho_q$ of the away ring therefore has order prime to $p$, which makes $p$ unramified there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicRings.lean#L382-L395

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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.CyclotomicRings
open scoped BigOperators

theorem OAI.CirculantHadamard.CyclotomicRings.prime_not_dvd_awayOrder (u p : ℕ) (hu : Odd u) (hp : p ∈ u.primeFactors) :
    ¬p ∣ awayOrder u p := by sorry
