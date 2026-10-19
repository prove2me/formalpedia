-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_card_even_subsets_eq_card_odd_subsets
-- name    : OAI.CirculantHadamard.card_even_subsets_eq_card_odd_subsets
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:41:58.217136+00:00
-- url     : https://prove2.me/theorems/785e2f76-1644-40eb-8f13-1debb4c59471
-- title:
--   A nonempty set has equally many even and odd subsets
-- statement:
--   Let $t$ be a nonempty finite set. Then
--   $$
--   \#\{S\subseteq t:|S|\text{ even}\}=\#\{S\subseteq t:|S|\text{ odd}\}.
--   $$
--
--   Consequently an alternating product over the subsets of $t$ has equally many numerator and denominator factors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingProducts.lean#L65-L94

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

open OAI OAI.CirculantHadamard
universe uI uG uH
open scoped BigOperators
variable {I : Type uI}

theorem OAI.CirculantHadamard.card_even_subsets_eq_card_odd_subsets (t : Finset I) (ht : t.Nonempty) :
    (t.powerset.filter (fun S => Even S.card)).card =
      (t.powerset.filter (fun S => Odd S.card)).card := by sorry
