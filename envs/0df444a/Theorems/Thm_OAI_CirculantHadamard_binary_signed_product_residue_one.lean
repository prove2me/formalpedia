-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_binary_signed_product_residue_one
-- name    : OAI.CirculantHadamard.binary_signed_product_residue_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:45:44.246315+00:00
-- url     : https://prove2.me/theorems/18ec726f-03cf-403c-b6c9-d30e64607b96
-- title:
--   Signed products of residue-one units have residue one
-- statement:
--   Let $\varphi:O\to k$ be a ring homomorphism into a field, $s$ a finite index set, $u_j$ units of $O$ with $\varphi(u_j)=1$ for $j\in s$, and $\varepsilon_j\in\mathbb Z$. Then
--   $$
--   \varphi\Bigl(\prod_{j\in s}u_j^{\varepsilon_j}\Bigr)=1,
--   $$
--   with negative powers formed in the unit group.
--
--   The units with residue one form a subgroup, so they are closed under arbitrary signed products.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryResidue.lean#L116-L135

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

open OAI OAI.CirculantHadamard
universe uO uk uIota
open scoped BigOperators
variable {O : Type uO} [CommRing O]
variable {k : Type uk} [Field k] [charTwo : CharP k 2]

omit charTwo in
theorem OAI.CirculantHadamard.binary_signed_product_residue_one [CharP k 2] {ι : Type uIota}
    (φ : O →+* k) (s : Finset ι) (u : ι → Oˣ) (ε : ι → ℤ)
    (hu : ∀ j ∈ s, φ (u j : O) = 1) :
    φ ((∏ j ∈ s, (u j) ^ (ε j) : Oˣ) : O) = 1 := by sorry
