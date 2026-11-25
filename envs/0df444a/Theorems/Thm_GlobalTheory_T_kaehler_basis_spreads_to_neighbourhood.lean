-- Prove2me | Theorems.Thm_GlobalTheory_T_kaehler_basis_spreads_to_neighbourhood
-- name    : GlobalTheory.T.kaehler_basis_spreads_to_neighbourhood
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:38.911024+00:00
-- url     : https://prove2.me/theorems/ea4ca0e2-cfcc-5a8e-903b-19639de79790
-- title:
--   T: kaehler basis spreads to neighbourhood
-- statement:
--   The T construction uses the kaehler basis spreads to neighbourhood property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisSpreadsToNeighbourhoodStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisSpreadsToNeighbourhoodStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhood
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhoodStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.kaehler_basis_spreads_to_neighbourhood : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A), (LinearIndependent (Localization.AtPrime P) (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧ Submodule.span (Localization.AtPrime P) (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) → ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := by sorry
