-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_alternatingProduct_prime_power_torsion
-- name    : OAI.CirculantHadamard.alternatingProduct_prime_power_torsion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T10:08:37.432901+00:00
-- url     : https://prove2.me/theorems/744c6dfb-36a7-46b2-965a-5c809de34cbe
-- title:
--   The alternating product has p-power order for each prime p dividing u
-- statement:
--   Let $u>1$ be odd, $B_u=\mathbb Z[i,\rho_q:q\mid u]\subseteq\mathbb C$ with $\rho_q=e^{2\pi i/q}$, and let $x\in\mathbb Z[i][\mathbb Z/u^2]$ satisfy $x\,x^{*}=u^2$, where $x^{*}(a)=\overline{x(-a)}$. For a set $S$ of primes dividing $u$ let $\xi_S\in B_u$ be the value of $x$ at the character $\chi_S(a)=\prod_{p\in S}\rho_p^{\,a\bmod p^{e_p}}$, and let $\mathcal A=\prod_S\xi_S^{(-1)^{|S|}}$ in the fraction field of $B_u$. Then for every prime $p\mid u$ there is $a\in\mathbb N$ with
--   $$
--   \mathcal A^{\,p^{a}}=1 .
--   $$
--
--   Since this holds for each prime divisor and $u$ is odd, the order of $\mathcal A$ is odd.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingTorsion.lean#L61-L95

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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjectionPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalComparison
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CoefficientEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAdjoin
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingTorsion

open OAI OAI.CirculantHadamard
open CyclotomicRings PrimeComponents PrimeCharacterEvaluations
open AlternatingLocalization

theorem OAI.CirculantHadamard.alternatingProduct_prime_power_torsion (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) :
    ∃ a : ℕ, (alternatingValue u (lt_trans Nat.zero_lt_one hu) x) ^ (p.val ^ a) = 1 := by sorry
