-- Prove2me | Theorems.Thm_MazurTransfer_Order13SameIntegralPicardFamilyRationalReductionMaps_actual_same_integral_picard_family_rational_reduction_maps
-- name    : MazurTransfer.Order13SameIntegralPicardFamilyRationalReductionMaps.actual_same_integral_picard_family_rational_reduction_maps
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T09:25:15.7396+00:00
-- url     : https://prove2.me/theorems/da6c791c-031b-46fe-8ee3-56aba9941000
-- title:
--   Rational reduction maps and integral lifts for one actual integral Picard family
-- statement:
--   Let $B=\mathbb Z[1/104]$ and let $X/B$ be the specified order-thirteen curve with its positive infinity section. There is a designated Picard scheme $D/B$ representing the algebraically trivial rigidified line bundles and carrying the specified abelian-scheme properties. For each $q\in\{3,5\}$, the relative point group $D(\mathbf F_q)$ is finite of order $19$, and there is a group homomorphism $$r_q:D(\mathbb Q)\longrightarrow D(\mathbf F_q).$$ Every rational point $a$ has a local integral lift $x\in D(\mathbb Z_{(q)})$ whose generic restriction is $a$ and whose finite-field restriction is $r_q(a)$. These are equalities of underlying scheme morphisms using the specified coefficient maps. Both reductions belong to this single family; this supplies the geometric maps for rational torsion bounds.
-- source:
--   Original complete actual_same_integral_picard_family_rational_reduction_maps contract and full proof body from MazurTheorem Order13SameIntegralPicardFamilyRationalReductionMaps.lean, Apache-2.0, Vas and contributors. The full original statement and proof body are unchanged, with public Definitions and the accepted integral-lift theorem replacing project imports. Native, strict and full frontend checks pass with standard axioms only, and the public and original closed types are kernel-compared. Uses the exact same integral Picard family, original abelian-scheme bundle and relative group law, actual mod-three and mod-five fibre counts and exact local scalar maps. Reuses official Anthropic FLT interfaces at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: same-family rational torsion bounds.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: one actual Picard abelian scheme over Z[1/104] has
rational specialization homomorphisms to its mod-three/mod-five groups
of cardinality nineteen; each map is specified by actual local extension.
Named downstream consumer: torsion injectivity and rational torsion bounds.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13SameIntegralPicardFamilyFiniteFibres
import Definitions.Def_MazurTransfer_Order13ActualRationalPicardSpecialization
import Theorems.Thm_MazurTransfer_Order13ActualRationalPicardSpecialization_rationalSpecializationHom_has_integral_lift
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections MazurTransfer.Order13IntegralBase
open MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres
open MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13ActualRationalPicardSpecialization

theorem MazurTransfer.Order13SameIntegralPicardFamilyRationalReductionMaps.actual_same_integral_picard_family_rational_reduction_maps :
    ∃ (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
      (h : RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
        (algEquivZeroCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)) D),
      AbelianSchemePropertyBundle BaseRing D.toBase ∧
      ∀ (q : ℕ) (hq : q=3 ∨ q=5),
        letI : Fact q.Prime := ⟨by rcases hq with rfl | rfl <;> decide⟩
        let L := (show RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
          (algEquivZeroGroupCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)).toSubPicCondition
            D from h).relativeGroupLaw
        letI := L.pointGroup (Spec.map (CommRingCat.ofHom canonicalRationalMap))
        letI := L.pointGroup (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq)))
        ∃ r : SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase →*
            SchemeHomOver (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq))) D.toBase,
          Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq))) D.toBase) ∧
          Nat.card (SchemeHomOver (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq))) D.toBase) = 19 ∧
          ∀ a, ∃ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (localBaseMap q hq))) D.toBase,
            Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) ℚ)) ≫ x.val = a.val ∧
            (r a).val = Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ x.val := by sorry
