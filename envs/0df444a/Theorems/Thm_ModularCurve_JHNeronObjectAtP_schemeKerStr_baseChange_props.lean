-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_schemeKerStr_baseChange_props
-- name    : ModularCurve.JHNeronObjectAtP.schemeKerStr_baseChange_props
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/d6c3c0d3-4d73-5c12-ba03-b3ca113ccfb5
-- title:
--   Finiteness, flatness and fibres of the m-kernel over A
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ satisfying `A.LiesOverPrime p`, i.e. the image of $p$ lies in the non-units of $A$, whose residue field is of characteristic $p$ and algebraically closed. Let $\Lambda$ be level data for $(p,M,H,A)$, which in particular provides the structure morphism $\sigma_A : \operatorname{Spec} A \to$ `base p` with `barPt A ≫ σA = genPt p`, and let $O$ be a `JHNeronObjectAtP` for these data: a scheme $G$ over `base p` whose structure morphism is smooth, separated, locally of finite type, quasi-compact and surjective with preconnected fibres, equipped with a relative group law $O.L$ whose point functor over the generic point is identified with $J_H(M)$ compatibly with addition, Galois action and Hecke operators, and for which multiplication by any $n > 0$ is flat and surjective. Let $m > 0$. Write $L_A :=$ `O.L.baseChange Λ.σA` for the group law obtained by base change along $\sigma_A$, and let `L_A.schemeKerStr m` be the projection to $\operatorname{Spec} A$ of the $m$-kernel `L_A.schemeKer m`, defined as the pullback of the $m$-fold multiplication morphism `L_A.schemeNsmul m` against the identity section. The assertion is a conjunction: this morphism is locally of finite type, separated, quasi-compact, flat and locally quasi-finite; there is a morphism $\pi$ from the $m$-kernel of the group law base-changed along `resPt A ≫ Λ.σA` (i.e. over the residue field of $A$) to `L_A.schemeKer m` making a pullback square of $\pi$ and the two kernel structure morphisms over $\operatorname{Spec}$ of the residue map $A \to \operatorname{ResidueField} A$; and there exist a scheme $X_K$, a morphism $q_K : X_K \to \operatorname{Spec} \overline{\mathbb{Q}}$ and a morphism $\pi_K : X_K \to$ `L_A.schemeKer m` forming a pullback square of $\pi_K$, $q_K$, `L_A.schemeKerStr m` and $\operatorname{Spec}$ of the inclusion $A \to \overline{\mathbb{Q}}$, with $X_K$ reduced.
--
--   This records the scheme-theoretic properties of the $m$-torsion kernel $G_A[m] \to \operatorname{Spec} A$ of the level-$\Gamma_H(M)$ Néron object at a place above $p$, together with the identification of its special fibre as the $m$-kernel of the residue-field law and the reducedness of its geometric generic fibre. It is the input for the counting of $m$-torsion points used in [`ModularCurve.JHNeronObjectAtP.natCard_finPts_eq_pow_of_representsRelSubPic`](thm.html#ModularCurve.JHNeronObjectAtP.natCard_finPts_eq_pow_of_representsRelSubPic) and [`ModularCurve.JHNeronObjectAtP.toricPts_le_finPts_and_finite_and_natCard_finPts_le`](thm.html#ModularCurve.JHNeronObjectAtP.toricPts_le_finPts_and_finite_and_natCard_finPts_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_schemeKerStr_baseChange_props.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.schemeKerStr_baseChange_props
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m) :
    LocallyOfFiniteType ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    IsSeparated ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    QuasiCompact ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    Flat ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    LocallyQuasiFinite ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    (∃ π : (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶ (O.L.baseChange Λ.σA).schemeKer m,
      IsPullback π ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)
        ((O.L.baseChange Λ.σA).schemeKerStr m) (Spec.map (CommRingCat.ofHom (residue ↥A)))) ∧
    (∃ (XK : Scheme.{0}) (qK : XK ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
        (πK : XK ⟶ (O.L.baseChange Λ.σA).schemeKer m),
      IsPullback πK qK ((O.L.baseChange Λ.σA).schemeKerStr m)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ)))) ∧ IsReduced XK) := by sorry
