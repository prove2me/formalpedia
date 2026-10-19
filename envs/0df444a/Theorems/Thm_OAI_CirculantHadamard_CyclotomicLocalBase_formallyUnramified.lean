-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_CyclotomicLocalBase_formallyUnramified
-- name    : OAI.CirculantHadamard.CyclotomicLocalBase.formallyUnramified
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T09:47:59.880991+00:00
-- url     : https://prove2.me/theorems/cfff39b9-9e26-43ae-ae5b-95a00038faf4
-- title:
--   The cyclotomic order is unramified at primes not dividing its level
-- statement:
--   Let $\eta\in\mathbb C$ be a primitive $L$th root of unity, $p$ a prime with $p\nmid L$, and $\mathfrak m$ a maximal ideal of $\mathbb Z[\eta]$ containing $p$. Then the localization $\mathbb Z[\eta]_{\mathfrak m}$ is formally unramified over $\mathbb Z$, i.e.
--   $$
--   \Omega_{\mathbb Z[\eta]_{\mathfrak m}/\mathbb Z}=0 .
--   $$
--
--   Differentiating $\eta^L=1$ kills $d\eta$ because $L$ is invertible at $\mathfrak m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicLocalBase.lean#L149-L164

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

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.CyclotomicLocalBase
universe uK uR uA
open IsLocalRing
variable {eta : ℂ} {L p : ℕ}

theorem OAI.CirculantHadamard.CyclotomicLocalBase.formallyUnramified (hη : IsPrimitiveRoot eta L) (hp : p.Prime)
    (hpL : ¬ p ∣ L) (m : Ideal (Order eta)) [m.IsMaximal]
    (hpm : (p : Order eta) ∈ m) : Algebra.FormallyUnramified ℤ (Local eta m) := by sorry
