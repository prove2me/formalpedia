-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_LocalComparison_projected_factor_divisible
-- name    : OAI.CirculantHadamard.LocalComparison.projected_factor_divisible
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T09:56:04.6782+00:00
-- url     : https://prove2.me/theorems/d73062a6-17c2-418e-aaf4-d74757a4bab7
-- title:
--   One projected factor of a p-power norm is divisible by p
-- statement:
--   Let $A$ be a commutative ring, $p$ a prime, $e\in\mathbb N$, and suppose $E=A[X]/(\Phi_{p^{e+2}}(X))$ is a discrete valuation ring with $p\ne0$ in $E$ and $v_E(p)=D>0$. Let $b$ be a unit of $A$ and $F,K\in A[\mathbb Z/p^{e+2}]$ with
--   $$
--   FK=p^{e+2}\,b .
--   $$
--
--   Then, writing $\pi$ for the projection to $A[\mathbb Z/p^{e+1}]$, either $\pi(F)=p\,F'$ or $\pi(K)=p\,K'$ for some element of $A[\mathbb Z/p^{e+1}]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicFactorDivision.lean#L25-L61

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

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalComparison
universe uA
open CyclicRing Polynomial IsDiscreteValuationRing
variable {A : Type uA} [CommRing A]

theorem OAI.CirculantHadamard.LocalComparison.projected_factor_divisible {p e D : ℕ} [NeZero p] (hp : p.Prime)
    [IsDomain (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))]
    [IsDiscreteValuationRing (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))]
    (hpS : (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) ≠ 0)
    (hD : 0 < D)
    (hpval : addVal (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))
      (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) = (D : ℕ∞))
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A))) :
    (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F') ∨
    (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
      scalar (p ^ (e + 1)) (p : A) * K') := by sorry
