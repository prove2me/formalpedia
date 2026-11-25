-- Prove2me | Theorems.Thm_GlobalTheory_SplitFinitePart_mem_of_forall_maximal
-- name    : GlobalTheory.SplitFinitePart.mem_of_forall_maximal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:27.847841+00:00
-- url     : https://prove2.me/theorems/a38c885f-e19a-40a8-9189-cb0c0dd4f58a
-- title:
--   Split Finite Part: mem of forall maximal
-- statement:
--   The Split Finite Part construction uses the mem of forall maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L287-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L287-L294

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

theorem GlobalTheory.SplitFinitePart.mem_of_forall_maximal {S : Type} [CommRing S] (U : (Sp S).Opens)
    (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → ∀ y, spMap (Ideal.Quotient.mk 𝔪) y ∈ U) (s : Sp S) : s ∈ U := by sorry
