-- Prove2me | Theorems.Thm_GlobalTheory_DegreeOneUniformiser_irreducible_of_valued
-- name    : GlobalTheory.DegreeOneUniformiser.irreducible_of_valued
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:53.823831+00:00
-- url     : https://prove2.me/theorems/86026a94-bfc2-4301-be6e-508988344f3d
-- title:
--   Degree One Uniformiser: irreducible of valued
-- statement:
--   The Degree One Uniformiser construction uses the irreducible of valued property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IrreducibleOfValued.lean#L16-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IrreducibleOfValued.lean#L16-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IrreducibleOfValued
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory
open GlobalTheory.DegreeOneUniformiser
open IsDedekindDomain NumberField

theorem GlobalTheory.DegreeOneUniformiser.irreducible_of_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F)
    (h : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) : Irreducible π := by sorry
