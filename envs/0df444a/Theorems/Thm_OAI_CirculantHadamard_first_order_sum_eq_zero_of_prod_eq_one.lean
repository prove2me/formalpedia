-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_first_order_sum_eq_zero_of_prod_eq_one
-- name    : OAI.CirculantHadamard.first_order_sum_eq_zero_of_prod_eq_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:43:21.991377+00:00
-- url     : https://prove2.me/theorems/be221e22-79d4-4fa8-8e71-3bdaa9a578f3
-- title:
--   First-order coefficients of a trivial product of principal units
-- statement:
--   Let $O$ be a domain, $t\in O$ nonzero, and $\varphi:O\to K$ a ring homomorphism into a field with $\varphi(t)=0$. Let $u_i=1+t\,L_i$ ($i\in s$) be units of $O$ and $\varepsilon_i\in\mathbb Z$. If
--   $$
--   \prod_{i\in s}u_i^{\varepsilon_i}=1,
--   $$
--   then $\sum_{i\in s}\varepsilon_i\,\varphi(L_i)=0$ in $K$.
--
--   To first order in $t$, a product of principal units is the sum of their coefficients, so a trivial product has vanishing first-order sum.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/FirstOrderResidue.lean#L102-L144

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

open OAI OAI.CirculantHadamard
universe uO uK uIota
open scoped BigOperators
variable {O : Type uO} [CommRing O]
variable [IsDomain O]
variable {K : Type uK} [Field K]

theorem OAI.CirculantHadamard.first_order_sum_eq_zero_of_prod_eq_one {ι : Type uIota}
    (φ : O →+* K) (t : O) (ht : t ≠ 0) (hφt : φ t = 0)
    (s : Finset ι) (u : ι → Oˣ) (L : ι → O) (ε : ι → ℤ)
    (hrep : ∀ i ∈ s, (u i : O) = 1 + t * L i)
    (hprod : (∏ i ∈ s, (u i) ^ (ε i)) = 1) :
    ∑ i ∈ s, (ε i : K) * φ (L i) = 0 := by sorry
