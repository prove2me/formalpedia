-- Prove2me | Theorems.Thm_GlobalTheory_SplitFinitePart_exists_open_fibres_subset
-- name    : GlobalTheory.SplitFinitePart.exists_open_fibres_subset
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:48.766008+00:00
-- url     : https://prove2.me/theorems/89e381da-8c23-4c34-b80b-5222aaa00bce
-- title:
--   Split Finite Part: exists open fibres subset
-- statement:
--   The Split Finite Part construction uses the exists open fibres subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L253-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L253-L262

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart

theorem GlobalTheory.SplitFinitePart.exists_open_fibres_subset {P S : Scheme.{0}} (W : S.Opens) (ρ : P ⟶ W.toScheme) [UniversallyClosed ρ]
    (U : P.Opens) (p : S) (hp : p ∈ W) (hU : ∀ y : P, (ρ y).1 = p → y ∈ U) :
    ∃ W' : S.Opens, p ∈ W' ∧ ∀ y : P, (ρ y).1 ∈ W' → y ∈ U := by sorry
