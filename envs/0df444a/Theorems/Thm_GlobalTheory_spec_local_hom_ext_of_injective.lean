-- Prove2me | Theorems.Thm_GlobalTheory_spec_local_hom_ext_of_injective
-- name    : GlobalTheory.spec_local_hom_ext_of_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:22:56.662795+00:00
-- url     : https://prove2.me/theorems/0bc803bc-9e36-4a17-b8cb-181074c0079c
-- title:
--   Global Theory: spec local hom ext of injective
-- statement:
--   The Global Theory construction uses the spec local hom ext of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecLocalRingHomExtOfInjectiveLocalHom.lean#L7-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecLocalRingHomExtOfInjectiveLocalHom.lean#L7-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecLocalRingHomExtOfInjectiveLocalHom
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

theorem GlobalTheory.spec_local_hom_ext_of_injective (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R →+* R') (hl : IsLocalHom φ) (hi : Function.Injective φ) (Y : Scheme.{0}) (x y : Sp R ⟶ Y)
    (h : spMap φ ≫ x = spMap φ ≫ y) : x = y := by sorry
