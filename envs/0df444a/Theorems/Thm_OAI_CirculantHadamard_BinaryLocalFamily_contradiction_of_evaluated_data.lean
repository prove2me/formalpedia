-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_BinaryLocalFamily_contradiction_of_evaluated_data
-- name    : OAI.CirculantHadamard.BinaryLocalFamily.contradiction_of_evaluated_data
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:47:03.318079+00:00
-- url     : https://prove2.me/theorems/2c98434b-12e3-45c8-8454-585c518a55b0
-- title:
--   No Gaussian norm data with odd-torsion alternating products
-- statement:
--   Let $u>0$ be odd, and let $C,D,G\in\mathbb Z[i][\mathbb Z/u^2]$ each satisfy $XX^{*}=u^2$. For a set $S$ of primes dividing $u$ write $X_S$ for the value at the subset character $\chi_S$ in $B_u=\mathbb Z[i,\rho_q:q\mid u]$, and let $J$ be the all-ones element. Suppose that for some $a_S,b_S,U_S\in B_u$ and all $S$
--   $$
--   C_S=a_S+b_S,\quad D_S=a_S-b_S,\quad G_S=a_S+ib_S-\bigl((1+i)J_S+2U_S\bigr),
--   $$
--   and that the alternating products $\prod_SX_S^{(-1)^{|S|}}$ for $X=C,D,G$ have odd order in the fraction field of $B_u$. Then we have a contradiction.
--
--   This is the concrete form of the binary contradiction, before the block data are constructed from a sign row.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryLocalFamily.lean#L31-L103

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

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.BinaryLocalFamily
open scoped BigOperators
open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing
open BinaryLocalRing BinaryProductTransport
variable (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u) (hodd : Odd u)

include hodd in
theorem OAI.CirculantHadamard.BinaryLocalFamily.contradiction_of_evaluated_data
    (C D G : Elem GaussianRing (u ^ 2))
    (hC : C * ringStar C = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hD : D * ringStar D = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hG : G * ringStar G = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (a b U : Finset (PrimeIndex u) → B u)
    (hc : ∀ S, subsetEvaluation u hu S C = a S + b S)
    (hd : ∀ S, subsetEvaluation u hu S D = a S - b S)
    (hg : ∀ S, subsetEvaluation u hu S G =
      a S + gaussianToB u gaussianI * b S -
        ((1 + gaussianToB u gaussianI) *
          subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing)) + 2 * U S))
    (hCodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S C))) ^ m = 1)
    (hDodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S D))) ^ m = 1)
    (hGodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S G))) ^ m = 1) :
    False := by sorry
