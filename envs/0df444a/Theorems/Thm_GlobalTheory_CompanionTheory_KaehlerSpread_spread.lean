-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KaehlerSpread_spread
-- name    : GlobalTheory.CompanionTheory.KaehlerSpread.spread
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:19.327243+00:00
-- url     : https://prove2.me/theorems/c51c5f0a-5651-4a80-8891-02031037bf13
-- title:
--   Kaehler Spread: spread
-- statement:
--   The Kaehler Spread construction uses the spread property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisSpreadsToNeighbourhood.lean#L35-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisSpreadsToNeighbourhood.lean#L35-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KaehlerSpread
open KaehlerDifferential

theorem GlobalTheory.CompanionTheory.KaehlerSpread.spread : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A), (LinearIndependent (Localization.AtPrime P) (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧ Submodule.span (Localization.AtPrime P) (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) → ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := by sorry
