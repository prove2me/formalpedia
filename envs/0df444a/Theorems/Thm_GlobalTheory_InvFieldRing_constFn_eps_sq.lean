-- Prove2me | Theorems.Thm_GlobalTheory_InvFieldRing_constFn_eps_sq
-- name    : GlobalTheory.InvFieldRing.constFn_eps_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:17:14.887883+00:00
-- url     : https://prove2.me/theorems/0c358777-8e87-5e88-afd0-315697c6ee0e
-- title:
--   Inv Field Ring: const Fn eps sq
-- statement:
--   The Inv Field Ring construction uses the const Fn eps sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L115-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L115-L117

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
noncomputable section
open GlobalTheory GlobalTheory.InvFieldRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.InvFieldRing.constFn_eps_sq {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp (DualNumber R)) (O : Y.Opens) :
    constFn p O DualNumber.eps * constFn p O DualNumber.eps = 0 := by sorry
