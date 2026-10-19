-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualRationalPicardSpecialization_rationalSpecializationHom_has_integral_lift
-- name    : MazurTransfer.Order13ActualRationalPicardSpecialization.rationalSpecializationHom_has_integral_lift
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T09:07:45.62122+00:00
-- url     : https://prove2.me/theorems/730b710d-6dbc-4368-9aa6-7f3f97c3fa93
-- title:
--   Actual rational Picard specialization comes from a local integral lift
-- statement:
--   Let $B=\mathbb Z[1/104]$, let $q=3$ or $5$, and let $D/B$ be a proper designated integral Picard scheme equipped with its specified relative group law $L$. For every relative rational point $a$ over the canonical map $B\to\mathbb Q$, there is a point $x$ over the actual map $B\to\mathbb Z_{(q)}$ such that $$i_q^*x=a,\qquad\overline{i}_q^*x=r_q(a).$$ Here $i_q:\operatorname{Spec}\mathbb Q\to\operatorname{Spec}\mathbb Z_{(q)}$, $\overline{i}_q:\operatorname{Spec}\mathbf F_q\to\operatorname{Spec}\mathbb Z_{(q)}$ are the specified maps and $r_q$ is the actual rational specialization homomorphism. Both identities are identities of the underlying scheme morphisms. This connects the constructed reduction map to local integral geometry for torsion specialization.
-- source:
--   Original complete rationalSpecializationHom_has_integral_lift contract and proof body from MazurTheorem Order13ActualRationalPicardSpecialization.lean, Apache-2.0, Vas and contributors. The original statement and full proof body are unchanged; the section variables are explicit and project imports become public Definitions. It uses the exact original group law, canonical rational/finite-field scalar maps and unique proper valuation-ring extension. The complete original closed type is kernel-compared with both the solution and public statement. Native, strict and full frontend checks pass with standard axioms only. Reuses original official Anthropic FLT relative-group interfaces at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: the same-family rational reduction maps, prime-to-residue-characteristic torsion detection and arithmetic specialization bounds.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual rational-to-mod-3/mod-5 group homomorphisms for
the original integral Picard family, obtained by unique local extension.
Named downstream consumer: prime-to-residue-characteristic torsion bounds.
No injectivity or rational rank conclusion is assumed or asserted here.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualRationalPicardSpecialization
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections MazurTransfer.Order13IntegralBase
open MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres
open MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.ProperRelativeGroupValuationSpecialization
open MazurTransfer.Order13ActualRationalPicardSpecialization

theorem MazurTransfer.Order13ActualRationalPicardSpecialization.rationalSpecializationHom_has_integral_lift (q : ℕ) [Fact q.Prime] (hq : q=3 ∨ q=5)
    (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
    (L : RelativeGroupLaw BaseRing D.toBase) [IsProper D.toBase]
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase) :
    ∃ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (localBaseMap q hq))) D.toBase,
      Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) ℚ)) ≫ x.val = a.val ∧
      (rationalSpecializationHom q hq D L a).val =
        Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ x.val := by sorry
