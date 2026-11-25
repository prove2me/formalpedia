-- Prove2me | Theorems.Thm_GlobalTheory_T_effCartier_restrict_iff_cartier_at
-- name    : GlobalTheory.T.effCartier_restrict_iff_cartier_at
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:20:19.389376+00:00
-- url     : https://prove2.me/theorems/96c9afb3-ceb3-48ec-b076-a278420248f3
-- title:
--   T: eff Cartier restrict iff cartier at
-- statement:
--   The T construction uses the eff Cartier restrict iff cartier at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/EffCartierRestrictIffCartierAtStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/EffCartierRestrictIffCartierAtStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierRestrictIffCartierAt
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierRestrictIffCartierAtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.effCartier_restrict_iff_cartier_at : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (O : X.Opens), FinalTheorems.EffCartier (J.comap O.ι) ↔ ∀ x ∈ O, CartAt J x := by sorry
