-- Prove2me | Theorems.Thm_GlobalTheory_OpenDim_ringKrullDim_affineOpen
-- name    : GlobalTheory.OpenDim.ringKrullDim_affineOpen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:59:00.333914+00:00
-- url     : https://prove2.me/theorems/353c9d6a-d355-4a1a-8b0a-85b79593ed63
-- title:
--   Open Dim: ring Krull Dim affine Open
-- statement:
--   The Open Dim construction uses the ring Krull Dim affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfIsIsoRestrict.lean#L14-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfIsIsoRestrict.lean#L14-L41

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OpenDim

theorem GlobalTheory.OpenDim.ringKrullDim_affineOpen (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
    ∃ d : ℕ, ringKrullDim Γ(Y, U) = d ∧ Algebra.trdeg F Y.functionField = d := by sorry
