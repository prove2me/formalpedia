-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_units_conj
-- name    : GlobalTheory.CompanionTheory.BlockIwahoriUML.units_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:10.792692+00:00
-- url     : https://prove2.me/theorems/f30296b4-7b78-4fc9-ae48-d9ff2f659a2d
-- title:
--   Block Iwahori UML: units conj
-- statement:
--   The Block Iwahori UML construction uses the units conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean#L176-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean#L176-L178

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BlockIwahoriUML
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]

theorem GlobalTheory.CompanionTheory.BlockIwahoriUML.units_conj {M : Type*} [Monoid M] (p q : Mˣ) (x : M) :
    ((p⁻¹ : Mˣ) : M) * ((p : M) * x * (q : M)) * ((q⁻¹ : Mˣ) : M) = x := by sorry
