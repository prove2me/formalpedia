-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_AlternatingLocalization_exists_base_of_edges_and_norm
-- name    : OAI.CirculantHadamard.AlternatingLocalization.exists_base_of_edges_and_norm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T10:00:18.477016+00:00
-- url     : https://prove2.me/theorems/53dcf813-2819-4b33-aac6-9a590b38d1ab
-- title:
--   An alternating product of norm factors is integral
-- statement:
--   Let $R$ be a domain with fraction field $K$, $u\ne0$, $t$ a finite set with a map $i\mapsto p_i$ hitting every prime divisor of $u$, and $x,y$ families in $R$ indexed by subsets of $t$ with $x(S)y(S)=u^2$. Assume that for every maximal ideal $\mathfrak m$ and every $i\in t$ with $p_i\in\mathfrak m$, each ratio $x(S\cup\{i\})/x(S)$ for $S\subseteq t\setminus\{i\}$ is the image of a unit of $R_{\mathfrak m}$ with residue one. Then
--   $$
--   \prod_{S\subseteq t}x(S)^{(-1)^{|S|}}\in R .
--   $$
--
--   The alternating product lies in every maximal localization, hence in the base ring.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingLocalization.lean#L291-L320

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
variable {I : Type uI} {R : Type uR} {K : Type uK} [DecidableEq I] [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

theorem OAI.CirculantHadamard.AlternatingLocalization.exists_base_of_edges_and_norm (u : ℕ) (hu : u ≠ 0)
    (t : Finset I) (prime : I → ℕ)
    (hcover : ∀ p ∈ u.primeFactors, ∃ i ∈ t, prime i = p)
    (x y : Finset I → R) (hnorm : ∀ S ⊆ t, x S * y S = (u : R) ^ 2)
    (hedge : ∀ m : MaximalSpectrum R, ∀ i ∈ t, (prime i : R) ∈ m.asIdeal →
      ∀ S ∈ (t.erase i).powerset, ∃ v : (AtMaximal R m)ˣ,
        toFraction K m (v : AtMaximal R m) =
          algebraMap R K (x (insert i S)) / algebraMap R K (x S) ∧
        IsLocalRing.residue (AtMaximal R m) (v : AtMaximal R m) = 1) :
    ∃ b : R, algebraMap R K b =
      alternatingProduct t (fun S => algebraMap R K (x S)) := by sorry
