-- Prove2me | Theorems.Thm_MazurTransfer_Order13SameIntegralPicardFamilyRationalTorsionBound_actual_same_integral_picard_family_rational_torsion_bound
-- name    : MazurTransfer.Order13SameIntegralPicardFamilyRationalTorsionBound.actual_same_integral_picard_family_rational_torsion_bound
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T10:20:46.431959+00:00
-- url     : https://prove2.me/theorems/6b2a5c4c-44e7-4f9d-a615-f082fac15eac
-- title:
--   The full rational torsion of one actual integral Picard family has order dividing nineteen
-- statement:
--   Let $B=\mathbb Z[1/104]$ and let $X/B$ be the literal order-thirteen curve with its positive infinity section. There exists one integral Picard scheme $D/B$ representing the algebraically trivial rigidified relative line bundles and carrying the specified abelian-scheme properties. Give $D(\mathbb Q)$ its commutative point-group structure induced by that representation and the canonical map $B\to\mathbb Q$. Its full torsion subgroup $T$ satisfies $$T\text{ is finite},\qquad |T|\mid19,\qquad a^{19}=1\ \text{for every }a\in D(\mathbb Q)\text{ of finite order}.$$ The bound uses the actual reductions of this same family modulo three and five, both with nineteen-element targets, and their verified prime-to-residue-characteristic torsion kernels. This supplies the upper bound for the actual arithmetic Picard torsion group.
-- source:
--   Original complete actual_same_integral_picard_family_rational_torsion_bound statement and main proof body from MazurTheorem Order13SameIntegralPicardFamilyRationalTorsionBound.lean, Apache-2.0, Vas and contributors. The original main statement and full proof body are unchanged. Three short group-theoretic consequences are derived inside the solution from the already Proved public torsion_card_dvd_nineteen_of_two_reductions theorem, avoiding a private abstract bound. Uses the accepted actual rational specialization torsion theorem and original same-family mod-three/mod-five counts. Complete original/public closed types are kernel-compared and native, strict and complete frontend checks pass with standard axioms only. The public statement preamble imports only its data/type dependencies. Reuses pinned official Anthropic FLT relative-group mechanisms at 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: the actual arithmetic Picard torsion bound.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the full rational torsion subgroup of one actual integral
Picard family is finite with order dividing nineteen.
Named downstream consumer: the actual arithmetic Picard torsion bound. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualRationalPicardSpecialization
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections Order13IntegralBase
open Order13SameIntegralPicardFamilyFiniteFibres Order13LocalIntegralCoefficientMaps
open Order13ActualRationalPicardSpecialization

theorem MazurTransfer.Order13SameIntegralPicardFamilyRationalTorsionBound.actual_same_integral_picard_family_rational_torsion_bound :
    ∃ (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
      (h : RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
        (algEquivZeroCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)) D),
      AbelianSchemePropertyBundle BaseRing D.toBase ∧
      let hG := (show RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
        (algEquivZeroGroupCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)).toSubPicCondition
          D from h)
      let L := hG.relativeGroupLaw
      letI : CommGroup (SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase) :=
        { L.pointGroup _ with mul_comm := hG.relativeGroupLaw_isCommutative _ }
      Finite (CommGroup.torsion (SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase)) ∧
      Nat.card (CommGroup.torsion (SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase)) ∣ 19 ∧
      ∀ a : SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase,
        IsOfFinOrder a → a ^ 19 = 1 := by sorry
