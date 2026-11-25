-- Prove2me | Theorems.Thm_GlobalTheory_HL_BadPlaces_bad_places
-- name    : GlobalTheory.HL.BadPlaces.bad_places
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:42.925038+00:00
-- url     : https://prove2.me/theorems/a5f274cf-f0a9-5664-8f22-832a1db3f7d4
-- title:
--   Bad Places: bad places
-- statement:
--   The Bad Places construction uses the bad places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GoodOfHpEqOne.lean#L239-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GoodOfHpEqOne.lean#L239-L274

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_Equality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoordinateLatticeUniqueTermAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GoodOfHpEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BadPlaces
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.BadPlaces.bad_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig), ∀ (r k : ℕ) (G : _root_.GlobalTheory.HL.GFrames A r k), 4 * r + 7 ≤ k → ∀ d Λ, G.IsTerm d Λ → G.Om.Finite ∧ (∀ p, 1 ≤ (G.S p).Hp) ∧ (∀ p ∈ G.Om, 2 ≤ (G.S p).q ∧ ((G.S p).q : ℝ) ≤ (G.S p).Hp) ∧ (2 : ℝ) ^ G.Om.ncard ≤ G.Ht ∧ ∀ p ∉ G.Om, (∀ d' Λ', (G.S p).IsTerm d' Λ' → (G.S p).BBzero d' Λ') ∧ ∀ d', (∃ Λ', (G.S p).IsTerm d' Λ') → ‖(G.S p).amp d' ((G.S p).BBzero d')‖ = 1 ∧ (G.S p).mass d' (fun _ => True) = 1 := by sorry
