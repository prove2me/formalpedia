-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_smoothLocus_specialPoint_eq_of_notMem_range_comp
-- name    : ModularCurve.XHDRModelAtP.exists_section_smoothLocus_specialPoint_eq_of_notMem_range_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/45bc4ec1-9928-56b8-8b4f-f95d975d7656
-- title:
--   Hensel lifting of a special point off one component
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis $hj$ that the Laurent series `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios at level one. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which equips the two-chart integral model `X p (ΓM M H) hj` over $\operatorname{Spec}(R\,p)$ with properness, flatness, integrality, local finite presentation and normality, with the level-$\Gamma_N$ data, with a curve model $\mathfrak{X}.\mathrm{Meta}$ of $\overline{\mathbb{Q}}(X_H)$ over $\overline{\mathbb{Q}}$ and an isomorphism $\mathfrak{X}.\mathrm{eeta}$ onto the geometric generic fibre compatible with the Galois action and with the pinning of the chart algebra, and with the further data of the special fibre recorded in that structure. Let $A \subseteq \overline{\mathbb{Q}}$ be a valuation subring with $p$ a nonunit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : R\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Let $i \neq j$ in $\mathrm{Fin}\,2$ and let $P$ be a closed point of the curve $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ whose image under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\,i$ does not lie in the image of the base map of $\mathfrak{X}.\mathrm{comp}\,j$. The conclusion asserts the existence of: a section $y$ of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$, that is a $\overline{\mathbb{Q}}$-point of $\mathfrak{X}.\mathrm{Meta}.C$; a morphism $u : \operatorname{Spec} A \to$ `X p (ΓM M H) hj` over $\operatorname{Spec}(R\,p)$, i.e. with $u$ followed by `toBase p (ΓM M H) hj` equal to $\operatorname{Spec}\rho$; and a morphism $u_\kappa$ from $\operatorname{Spec}$ of the residue field $\kappa$ of $A$ to the fibre `fibre ((residue A).comp ρ)`, the pullback of `toBase p (ΓM M H) hj` along $\operatorname{Spec}$ of the reduction $R\,p \to \kappa$, such that: the base change of $u$ along $A \hookrightarrow \overline{\mathbb{Q}}$ equals $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first pullback projection; the image of the base map of $u$ is contained in $\mathfrak{X}.\mathrm{smoothLocus}$ as a subset of the space of `X p (ΓM M H) hj`; the first component of $u_\kappa$ is $\operatorname{Spec}$ of the residue map followed by $u$; $u_\kappa$ is a section over $\operatorname{Spec}\kappa$; and the base map of $u_\kappa$ sends the closed point of $\operatorname{Spec}\kappa$ to the prescribed image of $P$.
--
--   This is the Hensel-lifting step for the Deligne–Rapoport type model at $p$: a closed point of the special fibre lying on one of the two components and off the other is a smooth point of the family, so, the valuation ring $A$ being henselian, it lifts to an $A$-section through the smooth locus, together with the associated $\overline{\mathbb{Q}}$-point of the geometric generic fibre. The resulting configuration data (generic point on $\mathfrak{X}.\mathrm{Meta}$, $A$-section in the smooth locus, prescribed special point on the $i$-th component) is what the point-reduction dictionary for the Néron model of $J_H(M)$ is applied to, in [`ModularCurve.JHNeronObjectAtP.mem_closure_gluedPic0_mk_configuredPair`](thm.html#ModularCurve.JHNeronObjectAtP.mem_closure_gluedPic0_mk_configuredPair) and in the order-of-vanishing computation [`ModularCurve.XHDRModelAtP.exists_ord_residue_eq_and_ord_eq_of_nonneg_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_ord_residue_eq_and_ord_eq_of_nonneg_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_section_smoothLocus_specialPoint_eq_of_notMem_range_comp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_section_smoothLocus_specialPoint_eq_of_notMem_range_comp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (i j : Fin 2) (hij : i ≠ j) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 ∉ Set.range (𝔛.comp A hA ρ hρ j).base) :
    ∃ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
      Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 ∧
      uκ ≫ pullback.snd _ _ = 𝟙 _ ∧
      (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by sorry
