-- Prove2me | Theorems.Thm_GlobalTheory_isIso_specMap_restrict_basicOpen_of_bijective
-- name    : GlobalTheory.isIso_specMap_restrict_basicOpen_of_bijective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:58.776804+00:00
-- url     : https://prove2.me/theorems/ae86a955-89b6-411c-abc4-fa7fcc68b67d
-- title:
--   Global Theory: is Iso spec Map restrict basic Open of bijective
-- statement:
--   The Global Theory construction uses the is Iso spec Map restrict basic Open of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelSpecMapIsIsoOverBasicOpen.lean#L9-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelSpecMapIsIsoOverBasicOpen.lean#L9-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option autoImplicit false
noncomputable section
open GlobalTheory

theorem GlobalTheory.isIso_specMap_restrict_basicOpen_of_bijective {R S : CommRingCat.{0}} (f : R ⟶ S) (r : R)
    (h : Function.Bijective (Localization.awayMap f.hom r)) :
    IsIso (Spec.map f ∣_ (PrimeSpectrum.basicOpen r : (Spec R).Opens)) := by sorry
