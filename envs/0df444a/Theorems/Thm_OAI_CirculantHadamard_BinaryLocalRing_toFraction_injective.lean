-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_BinaryLocalRing_toFraction_injective
-- name    : OAI.CirculantHadamard.BinaryLocalRing.toFraction_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:37:34.859094+00:00
-- url     : https://prove2.me/theorems/f825eeb4-6882-4f1c-89ae-d89178bffa77
-- title:
--   The local ring at two embeds in the fraction field
-- statement:
--   Let $u\in\mathbb N$, $B_u=\mathbb Z[i,\rho_q:q\mid u]\subseteq\mathbb C$, and $O_u$ its localization at the chosen maximal ideal containing $2$. The canonical map
--   $$
--   O_u\longrightarrow\operatorname{Frac}(B_u)
--   $$
--   is injective.
--
--   Identities between local units can therefore be checked in the fraction field, where the alternating products live.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryLocalRing.lean#L58-L69

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

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.BinaryLocalRing
open CyclotomicRings

theorem OAI.CirculantHadamard.BinaryLocalRing.toFraction_injective (u : ℕ) : Function.Injective (toFraction u) := by sorry
