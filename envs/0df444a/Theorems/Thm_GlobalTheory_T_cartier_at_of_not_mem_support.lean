-- Prove2me | Theorems.Thm_GlobalTheory_T_cartier_at_of_not_mem_support
-- name    : GlobalTheory.T.cartier_at_of_not_mem_support
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:27:01.286014+00:00
-- url     : https://prove2.me/theorems/453d1f03-b52a-4b73-be9b-e2219d34885c
-- title:
--   T: cartier at of not mem support
-- statement:
--   The T construction uses the cartier at of not mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartierAtOfNotMemSupportStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartierAtOfNotMemSupportStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfNotMemSupport
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfNotMemSupportStatement
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

theorem GlobalTheory.T.cartier_at_of_not_mem_support : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (x : X), x ∉ J.support → CartAt J x := by sorry
