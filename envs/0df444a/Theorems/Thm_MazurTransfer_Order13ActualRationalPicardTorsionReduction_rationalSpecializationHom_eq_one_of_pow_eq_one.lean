-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualRationalPicardTorsionReduction_rationalSpecializationHom_eq_one_of_pow_eq_one
-- name    : MazurTransfer.Order13ActualRationalPicardTorsionReduction.rationalSpecializationHom_eq_one_of_pow_eq_one
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T09:32:32.610489+00:00
-- url     : https://prove2.me/theorems/0c635069-c45a-4bfb-abeb-7b86dc662691
-- title:
--   Actual rational Picard specialization detects prime-to-residue-characteristic torsion
-- statement:
--   Let $B=\mathbb Z[1/104]$ and $q\in\{3,5\}$. Let $D/B$ be a proper designated integral Picard scheme with a commutative relative group law $L$, and write $r_q:D(\mathbb Q)\to D(\mathbf F_q)$ for the specified specialization homomorphism. For every natural number $m$ with $q\nmid m$ and every relative rational point $a$, $$a^m=1\quad\text{and}\quad r_q(a)=1\quad\Longrightarrow\quad a=1.$$ The point groups and scalar maps are those of the same integral family. This is the prime-to-residue-characteristic torsion detection step used to bound rational torsion from the two finite fibres.
-- source:
--   Original complete rationalSpecializationHom_eq_one_of_pow_eq_one contract and proof body from MazurTheorem Order13ActualRationalPicardTorsionReduction.lean, Apache-2.0, Vas and contributors. The original statement and main proof body are unchanged; four directly used structural helpers are retained inline under a fresh namespace. Public statement preamble contains imports and opens only. Complete original and public closed types are kernel-compared. Native, strict and full frontend checks pass with standard axioms only. Reuses the original official Anthropic FLT relative-group residue torsion kernel at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: the same-family rational torsion bound of nineteen. The public statement preamble imports only its type dependencies; proof-only residue-field and FLT torsion-kernel imports remain in the unchanged checked solution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the pinned Anthropic FLT relative-group residue torsion kernel theorem.
Design boundary: torsion detection by the actual mod-three and mod-five
specialization homomorphisms of the same integral Picard group.
Named downstream consumer: rational torsion bound of nineteen.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualRationalPicardSpecialization
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections MazurTransfer.Order13IntegralBase
open MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres
open MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13ActualRationalPicardSpecialization
open MazurTransfer.ProperRelativeGroupValuationSpecialization
open MazurTransfer.ValuationRingProperPointRestriction

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual finite-field map of Z localized at q reflects
residue restriction equalities and makes every q-coprime integer a unit.
Named downstream consumer: torsion injectivity of rational Picard specialization.
-/


noncomputable section

theorem MazurTransfer.Order13ActualRationalPicardTorsionReduction.rationalSpecializationHom_eq_one_of_pow_eq_one (q : ℕ) [Fact q.Prime] (hq : q=3 ∨ q=5)
    (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
    (L : RelativeGroupLaw BaseRing D.toBase) (hc : L.IsCommutative) [IsProper D.toBase] :
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom canonicalRationalMap))
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq)))
    ∀ (m : ℕ), ¬ q ∣ m →
      ∀ a : SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase,
      a ^ m = 1 → rationalSpecializationHom q hq D L a = 1 → a = 1 := by sorry
