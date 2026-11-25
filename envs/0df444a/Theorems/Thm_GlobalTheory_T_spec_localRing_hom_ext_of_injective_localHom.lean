-- Prove2me | Theorems.Thm_GlobalTheory_T_spec_localRing_hom_ext_of_injective_localHom
-- name    : GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:39:06.704861+00:00
-- url     : https://prove2.me/theorems/cea013d9-8c31-4c25-bf80-bd0f4b42372a
-- title:
--   T: spec local Ring hom ext of injective local Hom
-- statement:
--   The T construction uses the spec local Ring hom ext of injective local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecLocalRingHomExtOfInjectiveLocalHomStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecLocalRingHomExtOfInjectiveLocalHomStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecLocalRingHomExtOfInjectiveLocalHom
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecLocalRingHomExtOfInjectiveLocalHomStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R'), IsLocalHom φ → Function.Injective φ → ∀ (Y : Scheme.{0}) (x y : Sp R ⟶ Y), spMap φ ≫ x = spMap φ ≫ y → x = y := by sorry
