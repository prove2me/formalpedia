-- Prove2me | Theorems.Thm_GlobalTheory_T_cartier_at_of_locally_principal
-- name    : GlobalTheory.T.cartier_at_of_locally_principal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:06.888137+00:00
-- url     : https://prove2.me/theorems/2fc61f34-6108-45ea-a0a7-da1a2e18f93b
-- title:
--   T: cartier at of locally principal
-- statement:
--   The T construction uses the cartier at of locally principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartierAtOfLocallyPrincipalStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartierAtOfLocallyPrincipalStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfLocallyPrincipal
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfLocallyPrincipalStatement
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

theorem GlobalTheory.T.cartier_at_of_locally_principal : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData) (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by sorry
