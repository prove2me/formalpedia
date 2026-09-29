-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
-- name    : ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/867bb9d6-c213-53c5-81f1-b37b6ac0c33c
-- title:
--   Hensel lifting of a smooth special point to an A-section
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and the hypothesis $hj$ that the Laurent series $jqModC\ \mathbb{Q}$ lies in the intermediate field $qExpFunctionFieldC\ \mathbb{Q}\ \top$, so that the two-chart integral model $X\ p\ (\Gamma M\ M\ H)\ hj$ over $R\ p$ and its structure morphism `toBase` are defined. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which bundles the properness, flatness, integrality, normality and smoothness data for this model together with a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ and an isomorphism $\mathfrak{X}.\mathrm{eeta}$ of it with the base change of the model to $\overline{\mathbb{Q}}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R\ p \to A$ be a ring homomorphism compatible with the structure map $R\ p \to \overline{\mathbb{Q}}$ via the inclusion of $A$. Let $i \in \{0,1\}$ and let $P$ be a closed point of the scheme underlying $\mathfrak{X}.\mathrm{Mfib}\ A\ hA\ \rho\ h\rho$, and assume that the image of $P$ under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\ i$ and then the first projection of the fibre $\mathrm{pullback}(\mathrm{toBase}, \operatorname{Spec}(\kappa\text{-reduction of }\rho))$ lies in the open set $\mathfrak{X}.\mathrm{smoothLocus}$. The conclusion asserts the existence of a section $y$ of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ over $\operatorname{Spec}\overline{\mathbb{Q}}$ and of a morphism $u : \operatorname{Spec} A \to X\ p\ (\Gamma M\ M\ H)\ hj$ over $\operatorname{Spec}\rho$ (i.e. $u$ followed by `toBase` equals $\operatorname{Spec}\rho$) such that: the restriction of $u$ along $A \hookrightarrow \overline{\mathbb{Q}}$ equals $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection; the set-theoretic image of $u$ is contained in $\mathfrak{X}.\mathrm{smoothLocus}$; and there is a morphism $u_{\kappa}$ from $\operatorname{Spec}\kappa$ to the fibre of the model at the composite $R\ p \to A \to \kappa$ whose first projection is $u$ reduced modulo the maximal ideal, whose second projection is the identity, and which sends the closed point of $\operatorname{Spec}\kappa$ to the image of $P$ under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\ i$.
--
--   This is Hensel's lemma for smooth morphisms over a henselian local ring, applied to the Deligne–Rapoport style model of $X_H(M)$ at $p$: a $\kappa$-point of the special fibre lying in the smooth locus is the reduction of an $A$-valued section of the model that stays inside the smooth locus and has a prescribed $\overline{\mathbb{Q}}$-point as its generic fibre. It supplies the 'configured point' input to the Hecke and diamond compatibility statements on the special fibre of the Jacobian model, such as [`ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction`](thm.html#ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction) and [`ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull`](thm.html#ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (i : Fin 2) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) :
    ∃ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
      Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      ∃ uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 ∧
        uκ ≫ pullback.snd _ _ = 𝟙 _ ∧
        (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by sorry
