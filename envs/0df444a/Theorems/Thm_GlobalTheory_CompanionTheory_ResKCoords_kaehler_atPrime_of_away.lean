-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ResKCoords_kaehler_atPrime_of_away
-- name    : GlobalTheory.CompanionTheory.ResKCoords.kaehler_atPrime_of_away
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:33.75374+00:00
-- url     : https://prove2.me/theorems/96ca258c-ed6b-45ed-ac0c-55498c930b02
-- title:
--   Res KCoords: kaehler at Prime of away
-- statement:
--   The Res KCoords construction uses the kaehler at Prime of away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SmoothLocalRingFreeDifferentials.lean#L10-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SmoothLocalRingFreeDifferentials.lean#L10-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SmoothLocalRingFreeDifferentials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ResKCoords
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

theorem GlobalTheory.CompanionTheory.ResKCoords.kaehler_atPrime_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t))
    (P : Ideal A) [P.IsPrime] :
    Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by sorry
