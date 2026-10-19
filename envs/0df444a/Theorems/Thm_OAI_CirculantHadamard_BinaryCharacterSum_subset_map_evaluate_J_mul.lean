-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_BinaryCharacterSum_subset_map_evaluate_J_mul
-- name    : OAI.CirculantHadamard.BinaryCharacterSum.subset_map_evaluate_J_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:42:40.32514+00:00
-- url     : https://prove2.me/theorems/23f79d0c-f017-4c48-bf3c-0b0679c7c985
-- title:
--   Only the empty subset survives in the all-ones character sum
-- statement:
--   Let $I$ be a finite set, $n>0$, $\varphi:A\to R$ and $\psi:R\to T$ ring homomorphisms with $R$ a domain, and for each $S\subseteq I$ let $\chi_S$ be a character of $\mathbb Z/n$ with values in $R$. Assume $\chi_\varnothing$ is trivial and each $\chi_S$ with $S\ne\varnothing$ takes some value different from $1$. Let $J=\sum_{a\in\mathbb Z/n}e_a$ be the all-ones element of $A[\mathbb Z/n]$, and let $\varepsilon,d:\mathcal P(I)\to T$ with $\varepsilon(\varnothing)=1$. Then
--   $$
--   \sum_{S\subseteq I}\varepsilon(S)\,\psi\bigl(J(\chi_S)\bigr)\,d(S)=n\,d(\varnothing).
--   $$
--
--   Evaluating $J$ at a nontrivial character gives a vanishing character sum, so only the trivial character contributes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryCharacterSum.lean#L120-L147

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

open OAI OAI.CirculantHadamard
universe uG uR uA uI uT uK uk uB
open scoped BigOperators

theorem OAI.CirculantHadamard.BinaryCharacterSum.subset_map_evaluate_J_mul
    {I : Type uI} {A : Type uA} {R : Type uR} {T : Type uT} [Fintype I] [DecidableEq I] [CommRing A]
    [CommRing R] [IsDomain R] [CommRing T] {n : ℕ} [NeZero n]
    (φ : A →+* R) (ψ : R →+* T)
    (χ : Finset I → Multiplicative (ZMod n) →* R)
    (ε d : Finset I → T) (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1) :
    (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) =
      (n : T) * d ∅ := by sorry
