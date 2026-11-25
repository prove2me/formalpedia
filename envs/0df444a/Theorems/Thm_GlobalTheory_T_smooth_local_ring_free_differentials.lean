-- Prove2me | Theorems.Thm_GlobalTheory_T_smooth_local_ring_free_differentials
-- name    : GlobalTheory.T.smooth_local_ring_free_differentials
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:43.08216+00:00
-- url     : https://prove2.me/theorems/3c858e88-750b-5b36-a500-e69a6cb7328b
-- title:
--   T: smooth local ring free differentials
-- statement:
--   The T construction uses the smooth local ring free differentials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SmoothLocalRingFreeDifferentialsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SmoothLocalRingFreeDifferentialsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SmoothLocalRingFreeDifferentials
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SmoothLocalRingFreeDifferentialsStatement
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

theorem GlobalTheory.T.smooth_local_ring_free_differentials : ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g → ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime], letI := secAlgebra g U.1; Algebra.FinitePresentation K Γ(Y, U.1) ∧ Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by sorry
