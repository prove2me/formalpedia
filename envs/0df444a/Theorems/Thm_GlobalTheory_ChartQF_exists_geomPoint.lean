-- Prove2me | Theorems.Thm_GlobalTheory_ChartQF_exists_geomPoint
-- name    : GlobalTheory.ChartQF.exists_geomPoint
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:08:59.704308+00:00
-- url     : https://prove2.me/theorems/123d41ad-acec-45db-8867-eed44457e143
-- title:
--   Chart QF: exists geom Point
-- statement:
--   The Chart QF construction uses the exists geom Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L87-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L87-L148

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfMemClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartQF

theorem GlobalTheory.ChartQF.exists_geomPoint {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S) (p : Sp R)
    (hp : ξ p = ξ (closedPoint R)) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) K)
      (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ ∧ RingHom.ker ev = p.asIdeal ∧
      (∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap _ K (residue _ a)) ∧
      (∀ x, x ∈ k₀ ↔ IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) x) ∧
      (∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R)) ∧ ∃ P₀ : Sp k₀ ⟶ S, spMap k₀.subtype ≫ P₀ = spMap ev ≫ ξ := by sorry
