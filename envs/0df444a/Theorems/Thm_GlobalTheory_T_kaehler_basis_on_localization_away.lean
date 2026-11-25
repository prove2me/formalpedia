-- Prove2me | Theorems.Thm_GlobalTheory_T_kaehler_basis_on_localization_away
-- name    : GlobalTheory.T.kaehler_basis_on_localization_away
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:39.879196+00:00
-- url     : https://prove2.me/theorems/06fcffa7-3178-49b0-9679-1f5bf24485a2
-- title:
--   T: kaehler basis on localization away
-- statement:
--   The T construction uses the kaehler basis on localization away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisOnLocalizationAwayStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisOnLocalizationAwayStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisOnLocalizationAway
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisOnLocalizationAwayStatement
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

theorem GlobalTheory.T.kaehler_basis_on_localization_away : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ} (x : Fin n → Γ(Y, U.1)), (letI := secAlgebra g U.1; ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) → IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by sorry
