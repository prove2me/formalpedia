-- Prove2me | Theorems.Thm_GlobalTheory_T_blowup_of_agreeing_ideal_cartier
-- name    : GlobalTheory.T.blowup_of_agreeing_ideal_cartier
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:14:54.471773+00:00
-- url     : https://prove2.me/theorems/5ea58156-a190-43b0-9391-65e638951602
-- title:
--   T: blowup of agreeing ideal cartier
-- statement:
--   The T construction uses the blowup of agreeing ideal cartier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartierStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartierStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartier
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartierStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.blowup_of_agreeing_ideal_cartier : ∀ {X₁ X₂ : Scheme.{0}} (π : X₂ ⟶ X₁) (Z Z' : X₁.IdealSheafData) (O₁ O₂ : X₁.Opens), FinalTheorems.Blowup π Z → O₁ ⊔ O₂ = ⊤ → Z'.comap O₁.ι = Z.comap O₁.ι → (∀ x ∈ O₂, x ∉ Z'.support) → FinalTheorems.EffCartier (Z.comap O₂.ι) → FinalTheorems.Blowup π Z' := by sorry
