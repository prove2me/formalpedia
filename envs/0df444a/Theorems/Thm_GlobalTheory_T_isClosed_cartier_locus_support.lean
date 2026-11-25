-- Prove2me | Theorems.Thm_GlobalTheory_T_isClosed_cartier_locus_support
-- name    : GlobalTheory.T.isClosed_cartier_locus_support
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:47.196042+00:00
-- url     : https://prove2.me/theorems/5c78ccd0-5361-4034-9a8e-14e5c5013fc6
-- title:
--   T: is Closed cartier locus support
-- statement:
--   The T construction uses the is Closed cartier locus support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsClosedCartierLocusSupportStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsClosedCartierLocusSupportStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsClosedCartierLocusSupport
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsClosedCartierLocusSupportStatement
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

theorem GlobalTheory.T.isClosed_cartier_locus_support : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by sorry
