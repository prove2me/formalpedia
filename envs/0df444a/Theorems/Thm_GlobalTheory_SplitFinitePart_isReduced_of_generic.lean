-- Prove2me | Theorems.Thm_GlobalTheory_SplitFinitePart_isReduced_of_generic
-- name    : GlobalTheory.SplitFinitePart.isReduced_of_generic
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:51.990595+00:00
-- url     : https://prove2.me/theorems/f5351370-c49c-588c-ba17-56f49649de38
-- title:
--   Split Finite Part: is Reduced of generic
-- statement:
--   The Split Finite Part construction uses the is Reduced of generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L277-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L277-L285

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

theorem GlobalTheory.SplitFinitePart.isReduced_of_generic {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π] [IsReduced (pullback π (spMap (algebraMap R K)))] : IsReduced Z := by sorry
