-- Prove2me | Theorems.Thm_GlobalTheory_RelConstThickening_fromSpec_appLE_top
-- name    : GlobalTheory.RelConstThickening.fromSpec_appLE_top
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:01.521238+00:00
-- url     : https://prove2.me/theorems/bc9e84b0-e386-4cae-9e65-74e753ab754c
-- title:
--   Rel Const Thickening: from Spec app LE top
-- statement:
--   The Rel Const Thickening construction uses the from Spec app LE top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualNumberSectionsUniqueDecomposition.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualNumberSectionsUniqueDecomposition.lean#L61-L65

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.RelConstThickening

theorem GlobalTheory.RelConstThickening.fromSpec_appLE_top {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by sorry
