-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_AlternatingLocalization_actual_local_character_association
-- name    : OAI.CirculantHadamard.AlternatingLocalization.actual_local_character_association
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T10:01:52.863998+00:00
-- url     : https://prove2.me/theorems/ca6e68f3-310c-4da8-8184-3a40b766b13f
-- title:
--   Character values at rho and at one agree locally up to residue one
-- statement:
--   Let $f:A_0\to R$ be a ring homomorphism, $\mathfrak m$ a maximal ideal of $R$, and $p$ a prime with $p\in\mathfrak m$. Assume the localization $A$ of $A_0$ at $f^{-1}(\mathfrak m)$ is a characteristic-zero DVR with maximal ideal $(p)$. Let $\rho\in R$ be a root of $\Phi_p$, $n=p^{e+1}$, $c$ an integer that is a unit in $A$, and $F,K\in A_0[\mathbb Z/n]$ with $FK=p^{e+1}c$. Then in $R_{\mathfrak m}$
--   $$
--   F(\rho)=w\cdot F(1)
--   $$
--   for a unit $w$ of $R_{\mathfrak m}$ with residue $1$, where $F(\rho)=\sum_aF(a)\rho^{a}$ and $F(1)=\sum_aF(a)$ are evaluated through $f$.
--
--   This transports the abstract local comparison to the concrete coefficient rings.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingLocalization.lean#L345-L436

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
open CyclicRing
variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

theorem OAI.CirculantHadamard.AlternatingLocalization.actual_local_character_association
    (f : A₀ →+* R) (m : MaximalSpectrum R)
    [IsDomain (AtComap f m)] [CharZero (AtComap f m)]
    [IsDiscreteValuationRing (AtComap f m)]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpm : (p : R) ∈ m.asIdeal)
    (hmax : IsLocalRing.maximalIdeal (AtComap f m) =
      Ideal.span {(p : AtComap f m)})
    (rho : R) (hrho : rho ^ p = 1)
    (hroot : (Polynomial.cyclotomic p R).eval rho = 0)
    (n e c : ℕ) [NeZero n] (hn : n = p ^ (e + 1))
    (hrhon : rho ^ n = 1) (hc : IsUnit (c : AtComap f m))
    (F K : Elem A₀ n)
    (hFK : F * K = scalar n ((p : A₀) ^ (e + 1) * (c : A₀))) :
    LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal R m))
      (algebraMap R (AtMaximal R m)
        (evaluate f (CyclicPolynomial.powerCharacter n rho hrhon) F))
      (algebraMap R (AtMaximal R m) (evaluate f 1 F)) := by sorry
