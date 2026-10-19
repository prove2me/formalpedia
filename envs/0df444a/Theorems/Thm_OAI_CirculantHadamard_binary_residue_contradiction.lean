-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_binary_residue_contradiction
-- name    : OAI.CirculantHadamard.binary_residue_contradiction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:46:22.747645+00:00
-- url     : https://prove2.me/theorems/f50bc468-8678-4ba2-8ca1-86a0d50a9ece
-- title:
--   The first-order residue contradiction in characteristic two
-- statement:
--   Let $O$ be a domain with $2\ne0$, $i\in O$ with $i^2=-1$, and $\varphi:O\to k$ a ring homomorphism into a field of characteristic $2$ with $\varphi(i)=1$. For $j$ in a finite set $s$ let $c_j,d_j,g_j$ be units and $a_j,b_j,J_j,U_j\in O$ with
--   $$
--   c_j=a_j+b_j,\qquad d_j=a_j-b_j,\qquad g_j=a_j+ib_j-\bigl((1+i)J_j+2U_j\bigr),
--   $$
--   and let $\varepsilon_j\in\mathbb Z$. If both $\prod_j(d_j/c_j)^{\varepsilon_j}$ and $\prod_j(g_j/c_j)^{\varepsilon_j}$ have odd order, then $\sum_j\varepsilon_j\varphi(J_j/c_j)=0$.
--
--   So a nonzero residue sum $\sum_j\varepsilon_j\varphi(J_j/c_j)$ is incompatible with odd torsion of the two signed ratio products.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryResidue.lean#L139-L198

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
variable [IsDomain O]

theorem OAI.CirculantHadamard.binary_residue_contradiction {ι : Type uIota}
    (φ : O →+* k) (i : O) (hi : i ^ 2 = -1) (hφi : φ i = 1)
    (h2 : (2 : O) ≠ 0) (s : Finset ι) (ε : ι → ℤ)
    (c d g : ι → Oˣ) (a b J U : ι → O)
    (hc : ∀ j ∈ s, (c j : O) = a j + b j)
    (hd : ∀ j ∈ s, (d j : O) = a j - b j)
    (hg : ∀ j ∈ s,
      (g j : O) = a j + i * b j - ((1 + i) * J j + 2 * U j))
    (hrOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (d j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hwOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (g j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hnonzero : (∑ j ∈ s, (ε j : k) * φ (J j * (↑((c j)⁻¹) : O))) ≠ 0) :
    False := by sorry
