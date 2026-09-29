-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_abqFibre_one_comp_baseChange_hecke_U_eq_comp_relFrobenius_comp_abqFibre_one_of_not_sq_dvd
-- name    : ModularCurve.JHNeronObjectAtP.exists_abqFibre_one_comp_baseChange_hecke_U_eq_comp_relFrobenius_comp_abqFibre_one_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/8b714ebb-53e4-5cc4-936c-c23510a6ba6a
-- title:
--   Frobenius factorisation of Uₚ on the abelian-quotient coordinate
-- statement:
--   Arithmetic setting. Fix natural numbers $p$ (prime) and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and hypotheses `hpM : p ∣ M` and `hpM2 : ¬ p^2 ∣ M`, so that $p$ exactly divides $M$; `hHp` requires that every unit $u$ of $\mathbb{Z}/M$ whose image under the reduction `ZMod.unitsMap` to $(\mathbb{Z}/(M/p))^\times$ is trivial already lies in $H$, and $M/p \neq 0$. The hypothesis `hj` requires that the Laurent series `jqModC ℚ` lie in the field `qExpFunctionFieldC ℚ ⊤` of $q$-expansions at full level. Further, $\mathfrak{X}$ is a model structure `XHDRModelAtP p M H hpM hj` for the curve of level $\Gamma_M(H)$ over the ring `R p`; among its fields are the curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` together with the isomorphism $\mathfrak{X}.\mathrm{eeta}$ onto the generic geometric fibre, the smooth locus $\mathfrak{X}.\mathrm{smoothLocus}$, the morphisms $\mathfrak{X}.\pi$, $\mathfrak{X}.\pi_w$ and the involution $\mathfrak{X}.w$, the diamond automorphisms $\mathfrak{X}.\mathrm{dia}_0(e)$, and the curve model $\mathfrak{X}.\mathrm{Mfib}$ of the geometric special fibre with its comparison morphisms $\mathfrak{X}.\mathrm{efib}$ and $\mathfrak{X}.\mathrm{comp}$.
--
--   The place. $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, whose residue field $\kappa = \mathrm{ResidueField}\,A$ is of characteristic $p$ and algebraically closed. A ring homomorphism $\rho : \mathrm{R}\,p \to A$ is given with `hρ` asserting that $\rho$ followed by the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $\mathrm{R}\,p \to \overline{\mathbb{Q}}$.
--
--   The two Néron-type objects. $\Lambda$ is level data `JHNeronObjectAtP.LevelData p M H hpM A`: a base point $\Lambda.\sigma_A : \operatorname{Spec} A \to \mathrm{base}\,p$ lifting the generic point, a scheme $\Lambda.X$ with structure morphism $\Lambda.f$ to $\mathrm{base}\,p$ carrying a relative group law, a bijection $\Lambda.\mathrm{pts}$ from $J_H(M/p)$ at the subgroup `infSubgroup p M H hpM` (the image of $H$ in $(\mathbb{Z}/(M/p))^\times$) onto the sections of $\Lambda.f$ over the generic point, and a bijection $\Lambda.\mathrm{ptsSp}$ from $\mathrm{Pic}^0$ of the characteristic-$p$ function field `Fbar p M H hpM κ` onto the sections of $\Lambda.f$ over $\mathrm{resPt}\,A \gg \Lambda.\sigma_A$. $O$ is a Néron object `JHNeronObjectAtP p M H hpM A hA Λ` for $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \mathrm{xHFunctionFieldBar}\,M\,H)$, with total space $O.G$, structure morphism $O.g$, relative group law, point bijection $O.\mathrm{pts}$, Hecke endomorphisms $O.\mathrm{hecke}$ on the generators [`CohCarrier.Gen`](def/CohCarrier_Inst.html#L13), the special-fibre data $O.\mathrm{ssFinset}$, $O.\mathrm{ptsSp}$, $O.\mathrm{degPts}$ and the abelian-quotient coordinates $O.\mathrm{abqFibre}$. The hypothesis `hσA` requires $\Lambda.\sigma_A = \operatorname{Spec}(\rho)$.
--
--   Specialisation dictionary for $O$ (`hsp`). For each $i \in \{0,1\}$, given: two $\overline{\mathbb{Q}}$-points $y_1, y_2$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base; $A$-points $u_1, u_2$ of the model over $\operatorname{Spec}(\rho)$ whose base changes along $\mathrm{barPt}\,A$ agree with $y_1, y_2$ transported through $\mathfrak{X}.\mathrm{eeta}$ and whose topological images lie in $\mathfrak{X}.\mathrm{smoothLocus}$; $\kappa$-points $u\kappa_1, u\kappa_2$ of the fibre `fibre ((residue A).comp ρ)` which are sections of the fibre projection and reduce $u_1, u_2$; closed points $P_1, P_2$ of $\mathfrak{X}.\mathrm{Mfib}$ whose images under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\,i$ are the closed points determined by $u\kappa_1, u\kappa_2$; a degree-zero divisor $Dv$ on `xHFunctionFieldBar M H` equal to the difference of the places attached to $y_1$ and $y_2$ by $\mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}$; and an element $x$ of the admissible gluing data over $O.\mathrm{ssFinset}$ whose first divisor component is the difference of the places of $P_1$ and $P_2$ when $i = 0$ and zero otherwise, whose second divisor component is that same difference when $i = 1$ and zero otherwise, and whose third component (the family indexed by $O.\mathrm{ssFinset}$ with values in $\mathrm{Additive}\,\kappa^\times$) is zero — then there exists a section $s$ of $O.g$ over $\Lambda.\sigma_A$ such that $O.\mathrm{pts}(\mathrm{Pic}^0[Dv])$ is $\mathrm{barPt}\,A$ followed by $s$, and $O.\mathrm{ptsSp}^{-1}$ of the restriction of $s$ along $\mathrm{resPt}\,A$ is the class of $x$ in `GluedPic0`.
--
--   Specialisation dictionary for $\Lambda$ (`hspΛ`). For each $i \in \{0,1\}$, given: $\overline{\mathbb{Q}}$-points $y_1, y_2$ with $A$-points $u_1, u_2$ over $\operatorname{Spec}(\rho)$ compatible with them through $\mathfrak{X}.\mathrm{eeta}$ (no condition on the image lying in the smooth locus is imposed here); $\kappa$-points $u\kappa_1, u\kappa_2$ of the fibre which are sections of the fibre projection and reduce $u_1, u_2$; closed points $Q_1, Q_2$ of $\mathfrak{X}.\mathrm{Mfib}$ whose images under $\mathfrak{X}.\mathrm{efib}$ are the closed points obtained from $u\kappa_1, u\kappa_2$ by the fibre map of $\mathfrak{X}.\pi$ when $i = 0$ and of $\mathfrak{X}.\pi_w$ otherwise; a degree-zero divisor $Dv$ equal to the difference of the places of $y_1$ and $y_2$; and a degree-zero divisor $Dw$ on `Fbar p M H hpM κ` equal to the difference of the places of $Q_1$ and $Q_2$ — then there exists a section $s_0$ of $\Lambda.f$ over $\Lambda.\sigma_A$ with $\Lambda.\mathrm{pts}(O.\mathrm{degPts}\,i\,(\mathrm{Pic}^0[Dv]))$ equal to $\mathrm{barPt}\,A$ followed by $s_0$, and $\Lambda.\mathrm{ptsSp}^{-1}$ of the restriction of $s_0$ along $\mathrm{resPt}\,A$ equal to the class of $Dw$.
--
--   Diamonds on the special fibre (`hdia0`). For every unit $e$ of $\mathbb{Z}/(M/p)$ and every closed point $P$ of $\mathfrak{X}.\mathrm{Mfib}$, the point obtained by transporting $P$ through $\mathfrak{X}.\mathrm{efib}$, applying the fibre map of the automorphism $\mathfrak{X}.\mathrm{dia}_0(e)$ and returning along the inverse of $\mathfrak{X}.\mathrm{efib}$ is again a closed point, and its place is the image of the place of $P$ under the semilinear automorphism attached by `SemilinearAut.ofAlgAut` to `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at [`CuspForm.gammaLift (M/p) e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36).
--
--   Frobenius data. Additive endomorphisms $F$, $F^{-1}$, $F^{*}$ of $\mathrm{Pic}^0(\kappa, \mathrm{Fbar}\,p\,M\,H\,hpM\,\kappa)$ are given with: `hF`, that $F$ is `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p`; `hFinv`, that $F$ and $F^{-1}$ are mutually inverse; and `hFstar`, that $F^{*}z = p \cdot F^{-1}z$. A unit $pb$ of $\mathbb{Z}/(M/p)$ is given with `hpb` asserting that its underlying residue is $p$, together with an additive endomorphism $\delta$ and `hδ` asserting that $\delta$ is the action of the diamond semilinear automorphism attached to [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) as above.
--
--   Degeneracy data. $\alpha\mathrm{pull} : \{0,1\} \to \mathrm{Hom}(J_H(M/p), J_H(M))$ and $\mathrm{degPull} : \{0,1\} \to \{\varphi : \Lambda.X \to O.G \mid \varphi \gg O.g = \Lambda.f\}$ are given, with `hpull` requiring that $O.\mathrm{pts}(\alpha\mathrm{pull}\,i\,x)$ be $\Lambda.\mathrm{pts}(x)$ followed by $\mathrm{degPull}\,i$ for all $i$ and $x$, and `hpullsp` requiring that for every section $x$ of $\Lambda.f$ over $\mathrm{resPt}\,A \gg \Lambda.\sigma_A$ the image under `GluedPic0.toPic0Pair` of $O.\mathrm{ptsSp}^{-1}$ applied to ($x$ followed by $\mathrm{degPull}\,i$) be $(\Lambda.\mathrm{ptsSp}^{-1}x,\; F^{*}\Lambda.\mathrm{ptsSp}^{-1}x)$ when $i = 0$ and $(F^{*}\Lambda.\mathrm{ptsSp}^{-1}x,\; \delta\,\Lambda.\mathrm{ptsSp}^{-1}x)$ otherwise.
--
--   Atkin–Lehner and $U_p$ pins. An additive endomorphism $\bar W$ of $J_H(M)$ and a semilinear automorphism $w_{\mathrm{gen}}$ of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ are given, with `hWbar` asserting that $\bar W$ is the action of $w_{\mathrm{gen}}$, and `hwgen` asserting that whenever two geometric points $y, y'$ satisfy that $y'$ transported through $\mathfrak{X}.\mathrm{eeta}$ and then $\mathfrak{X}.w$ equals $y$ transported through $\mathfrak{X}.\mathrm{eeta}$, the place of $y'$ is $w_{\mathrm{gen}}$ applied to the place of $y$. A set $S \subseteq \mathbb{N}$ is given, with `hUPgen` asserting that for all $x \in J_H(M)$ one has $\mathrm{genOpH}\,M\,H\,S(U_p)x + \bar W x = \alpha\mathrm{pull}\,1\,(O.\mathrm{degPts}\,0\,x)$.
--
--   Characteristic-$p$ data for the Frobenius. Writing $\iota = \mathrm{resPt}\,A \gg \Lambda.\sigma_A$, the hypothesis `hp0` asserts that $p$ vanishes in the global sections of the base change `RelativeGroupLaw.baseChangeScheme ι Λ.f`, and `hFrobΛ` asserts that the $p$-power Frobenius `Scheme.frobenius … p 1` of that base change, followed by the projection to $\Lambda.X$ and then $\Lambda.f$, equals the projection to $\operatorname{Spec}\kappa$ followed by $\iota$.
--
--   Conclusion. There exists an endomorphism $D$ of `RelativeGroupLaw.baseChangeStr ι Λ.f` over $\operatorname{Spec}\kappa$ such that the base change along $\iota$ of the Hecke endomorphism $O.\mathrm{hecke}\,S\,(U_p)$ of $O.g$ — namely `pullback.map` of that morphism with identities on the base — followed by $O.\mathrm{abqFibre}\,1$ equals $O.\mathrm{abqFibre}\,1$ followed by the endomorphism of `baseChangeStr ι Λ.f` obtained from the Frobenius (the map to the pullback with components the Frobenius followed by the projection to $\Lambda.X$, and the projection to $\operatorname{Spec}\kappa$) followed by $D$. Equivalently, $\mathrm{abq}_1 \circ (U_p)_\kappa = D \circ \mathrm{Frob} \circ \mathrm{abq}_1$ as morphisms from the base-changed $O.g$ to the base-changed $\Lambda.f$ over $\operatorname{Spec}\kappa$. No further property of $D$ is asserted.
--
--   This is the scheme-theoretic form, on the geometric special fibre at $p \| M$, of the lower-right entry of Ribet's upper-triangular description of $U_p$ on the Jacobian of $X_H(M)$: on the abelian-quotient coordinate indexed by $1$, the Hecke operator $U_p$ becomes Frobenius followed by a diamond-type endomorphism, here produced as an unspecified endomorphism $D$ of the base-changed level-$(M/p)$ scheme. It promotes the corresponding identity on $\kappa$-points to an identity of morphisms of schemes, using reducedness and rigidity for morphisms out of a reduced scheme of finite type over an algebraically closed field, and is used in the study of the ordinary part of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_abqFibre_one_comp_baseChange_hecke_U_eq_comp_relFrobenius_comp_abqFibre_one_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.JHNeronObjectAtP.exists_abqFibre_one_comp_baseChange_hecke_U_eq_comp_relFrobenius_comp_abqFibre_one_of_not_sq_dvd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (S : Set ℕ)
    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (hp0 : (p : Γ((RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f), ⊤)) = 0)

    (hFrobΛ : (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f) p 1 Fact.out hp0 ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA)) ≫ Λ.f =
      pullback.snd Λ.f (resPt A ≫ Λ.σA) ≫ (resPt A ≫ Λ.σA)) :
    ∃ D : SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f),
    NeronModelInfra.schemeHomOverComp
        (⟨pullback.map O.g (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).2).symm)
            (by rw [Category.comp_id, Category.id_comp]),
          by rw [RelativeGroupLaw.baseChangeStr, pullback.lift_snd, Category.comp_id]⟩ :
          SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
        (O.abqFibre 1) =
      NeronModelInfra.schemeHomOverComp (O.abqFibre 1)
        (NeronModelInfra.schemeHomOverComp
          (⟨pullback.lift (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f) p 1 Fact.out hp0 ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA)) (pullback.snd Λ.f (resPt A ≫ Λ.σA)) hFrobΛ,
            pullback.lift_snd _ _ _⟩ :
            SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
          D) := by sorry
