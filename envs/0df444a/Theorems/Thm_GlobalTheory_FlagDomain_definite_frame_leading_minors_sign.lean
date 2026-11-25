-- Prove2me | Theorems.Thm_GlobalTheory_FlagDomain_definite_frame_leading_minors_sign
-- name    : GlobalTheory.FlagDomain.definite_frame_leading_minors_sign
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:42:22.096273+00:00
-- url     : https://prove2.me/theorems/e3e3cf03-077e-4f39-a53c-5cd472c34b11
-- title:
--   Flag Domain: definite frame leading minors sign
-- statement:
--   The Flag Domain construction uses the definite frame leading minors sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DefiniteFrameLeadingMinorsSign.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DefiniteFrameLeadingMinorsSign.lean#L78-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DefiniteFrameLeadingMinorsSign
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexOrder ComplexConjugate Matrix
open GlobalTheory GlobalTheory.FlagDomain

theorem GlobalTheory.FlagDomain.definite_frame_leading_minors_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ (x : Frame X.Ψ r) (τ : X.Ψ), (mat x τ).det ≠ 0 →
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by sorry
