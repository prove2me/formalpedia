-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_AlternatingLocalization_exists_integral_alternatingProduct
-- name    : OAI.CirculantHadamard.AlternatingLocalization.exists_integral_alternatingProduct
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T10:05:01.648153+00:00
-- url     : https://prove2.me/theorems/b9a4bcbf-7643-4fe0-a7c8-c38b7ef0007b
-- title:
--   The alternating product of subset character values is integral
-- statement:
--   Let $u>0$ be odd, $B_u=\mathbb Z[i,\rho_q:q\mid u]\subseteq\mathbb C$, and $x\in\mathbb Z[i][\mathbb Z/u^2]$ with $x\,x^{*}=u^2$. With $\xi_S$ the value of $x$ at the subset character $\chi_S$ for each set $S$ of primes dividing $u$, there is $z\in B_u$ with
--   $$
--   z=\prod_{S}\xi_S^{\,(-1)^{|S|}}\quad\text{in }\operatorname{Frac}(B_u).
--   $$
--
--   Although formed with divisions, the alternating product lies in $B_u$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingLocalization.lean#L556-L577

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

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.AlternatingLocalization
universe uR uK uAZero uS uL uI uk
open scoped BigOperators
open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing

theorem OAI.CirculantHadamard.AlternatingLocalization.exists_integral_alternatingProduct (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    ∃ z : B u, algebraMap (B u) (FractionRing (B u)) z =
      alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x)) := by sorry
