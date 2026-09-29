-- Prove2me | Theorems.Thm_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP
-- name    : ModularCurve.exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/772282a8-6d51-5c6e-923f-5f86a1e6ed53
-- title:
--   Finite part at p descends to the decomposition ring
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and a subgroup $H \le (\mathbb{Z}/M)^{\times}$ containing the kernel of the reduction map $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$, i.e. every unit $u$ with `ZMod.unitsMap` image $1$ lies in $H$ (`hHp`); $M/p$ is nonzero. Fix further a valuation subring $Pl$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $p$ a non-unit of $Pl$ (`hPl`, the predicate `LiesOverPrime`), whose residue field has characteristic $p$ and is algebraically closed, and the hypothesis `hj` that the Laurent series `jqModC ℚ` lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of $\mathbb{Q}((q))$ attached to the full group $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a model datum [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81) for the two-chart integral models of the modular curves of levels `ΓM M H` and `ΓN p M H hpM` over the base ring $R =$ [`ModularCurve.XHDRLevel.R p`](def/ModularCurve_XHDRModelAtP.html#L22), let $\Lambda$ be level data [`ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl`](def/ModularCurve_JHNeronObjectAtP.html#L32), and let $O$ be a Néron object [`ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ`](def/ModularCurve_JHNeronObjectAtP.html#L53), so that $O$ consists of a scheme $O.G$ with structure morphism $O.g$ to $\operatorname{Spec} R$, a commutative relative group law $O.L$ on $O.g$, a dictionary $O.\mathrm{pts}$ between $J_H(M) = \mathrm{Pic}^0$ of the function field of $X_H(M)$ over $\overline{\mathbb{Q}}$ and generic sections of $O.g$, together with the further clauses of that structure.
--
--   Two representability hypotheses are assumed. `hrep` asserts that the relative $\mathrm{Pic}^0$ designation formed from $O.G$, $O.g$ and the unit section of $O.L$ over the identity of $\operatorname{Spec} R$ represents, in the sense of `RepresentsRelSubPic` (a Poincaré rigidified line bundle satisfying the condition, the universal property that every rigidified line bundle satisfying the condition is the pullback of the Poincaré bundle along a unique section, and a trivialisation along the zero section), the subfunctor of the relative Picard functor of the model `toBase p (ΓM M H) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ cut out by `algEquivZeroCut`, the condition that the restriction to every geometric fibre be algebraically equivalent to zero. Likewise `hrepΛ` asserts that the designation formed from $\Lambda.X$, $\Lambda.f$ and the unit section of $\Lambda.L$ represents the corresponding `algEquivZeroCut` subfunctor for the model `toBase p (ΓN p M H hpM) hj`, rigidified along the section obtained by composing $\mathfrak{X}.\varepsilon_{\inf}$ with $\mathfrak{X}.\pi$.
--
--   Next, $R_h$ is a henselian local domain which is a $\overline{\mathbb{Q}}$-algebra with injective structure map, whose image in $\overline{\mathbb{Q}}$ lies in $Pl$ (`hRA`) and whose maximal ideal consists exactly of the elements whose images have $Pl$-valuation $< 1$ (`hRloc`). Over $R_h$ there is given a $p$-divisible group $\mathcal{G} =$ [`PDivisibleGroup Rh p h`](def/PDivisibleGroup_Basic.html#L199) of height $h$, that is, a system of finite free cocommutative Hopf $R_h$-algebras $\mathcal{G}.\mathrm{level}\,v$ of rank $p^{vh}$ with surjective bialgebra transition maps whose kernels are the $p^v$-torsion ideals; a ring homomorphism $\rho_h : R \to R_h$ compatible with the embeddings into $\overline{\mathbb{Q}}$ (`hρh`); and morphisms $\iota_v : \operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v) \to O.G$ for all $v$, subject to the following clauses: `hιbase`, that $\iota_v$ followed by $O.g$ is the structure morphism $\operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v) \to \operatorname{Spec} R_h$ followed by $\operatorname{Spec}\rho_h$; `hιcl`, that the resulting morphism into the pullback of $O.g$ along $\operatorname{Spec}\rho_h$ is a closed immersion; `hιp`, that $\iota_v$ followed by multiplication by $p^v$ for $O.L$ equals $\iota_v \ggg O.g$ followed by the unit section, so that $\iota_v$ lands in the $p^v$-torsion; `hιmul`, that $\iota_v$ is a homomorphism, in the sense that for every commutative $R_h$-algebra $B$ and all $B$-points $x,y$ of $\mathcal{G}$ at level $v$ whose associated morphisms lie over the base (hypotheses $hx$, $hy$), the morphism associated with $x \cdot y$ is the $O.L$-product of those associated with $x$ and $y$; `hιt`, compatibility of the $\iota_v$ with the transition maps of $\mathcal{G}$; and `hιfin`, which states for each $v$, given the torsion clause $h3$ and the base clause $h4$, that the induced morphism $j_v$ from $\operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v)$ to the pullback along $\operatorname{Spec}\rho_h$ of the $p^v$-torsion subscheme of $O.G$ is simultaneously an open immersion and a closed immersion, and that every point of that pullback lying over the closed point of $R_h$ is in the range of $j_v$ on underlying spaces.
--
--   The points dictionary for $\mathcal{G}$ consists of an additive map $\Delta : \mathcal{G}.\mathrm{Points}(\overline{\mathbb{Q}}) \to J_H(M)$ with: `hΔinj`, injectivity; `hΔlev`, that for every $v$ a class $y$ lies in $O.\mathrm{finPts}(p^v)$ — the subgroup generated by the $p^v$-torsion classes whose associated section extends over the place $\Lambda.\sigma_A$ — precisely when $y = \Delta$ of the class of some level-$v$ point of $\mathcal{G}$ over $\overline{\mathbb{Q}}$; `hΔgal`, equivariance, namely $\Delta(\tau' \cdot z) = \tau \cdot \Delta(z)$ whenever $\tau$ is a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ and $\tau'$ an $R_h$-automorphism of $\overline{\mathbb{Q}}$ with the same underlying function; `htor`, that every element of $O.\mathrm{toricPts}(p^v)$ is likewise $\Delta$ of a level-$v$ point; and `hιpts`, that the section $O.\mathrm{pts}$ attached to $\Delta$ of the class of a level-$v$ point $x$ is $\operatorname{Spec}$ of the algebra homomorphism of $x$ followed by $\iota_v$.
--
--   Finally, write $R_D$ for the intersection $Pl \cap \overline{\mathbb{Q}}^{D}$, i.e. `Pl.toSubring ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring`; it is assumed that $R_h$ is an $R_D$-algebra forming a scalar tower $R_D \to R_h \to \overline{\mathbb{Q}}$ and that $R_D$ is a discrete valuation ring. Over $R_D$ there is given a $p$-divisible group $\mathcal{G}^D =$ [`PDivisibleGroup RD p h`](def/PDivisibleGroup_Basic.html#L199) of the same height $h$, with: an injective additive map $\Delta^D : \mathcal{G}^D.\mathrm{Points}(\overline{\mathbb{Q}}) \to J_H(M)$ (`hΔDinj`) whose level-$v$ image is exactly $O.\mathrm{finPts}(p^v)$ (`hΔDlev`) and which is equivariant for $\mathbb{Q}$-automorphisms of $\overline{\mathbb{Q}}$ and $R_D$-automorphisms inducing them (`hΔDgal`); the inclusion $O.\mathrm{toricPts}(p^v) \le O.\mathrm{finPts}(p^v)$ for all $v$ (`htorD`); a ring homomorphism $\rho_D : R \to R_D$ compatible with the embeddings into $\overline{\mathbb{Q}}$ (`hρD`); and morphisms $\iota^D_v : \operatorname{Spec}(\mathcal{G}^D.\mathrm{level}\,v) \to O.G$ satisfying the exact analogues of the clauses above, namely base compatibility (`hιDbase`), closed immersion into the pullback of $O.g$ along $\operatorname{Spec}\rho_D$ (`hιDcl`), landing in the $p^v$-torsion (`hιDp`), the homomorphism clause over arbitrary commutative $R_D$-algebras (`hιDmul`), compatibility with transitions (`hιDt`), the open-and-closed-immersion property of the induced morphism $j_v$ into the pullback along $\operatorname{Spec}\rho_D$ of the $p^v$-torsion subscheme together with the requirement that all points over the closed point of $R_D$ be in its range (`hιDfin`), and the identification of the sections $O.\mathrm{pts} \circ \Delta^D$ with $\operatorname{Spec}$ of the algebra homomorphisms of points followed by $\iota^D_v$ (`hιDpts`).
--
--   Under these hypotheses there exists a family of $R_h$-bialgebra isomorphisms
--   $$e_v : \mathcal{G}.\mathrm{level}\,v \;\xrightarrow{\ \sim\ }\; (\mathcal{G}^D.\mathrm{baseChange}\,R_h).\mathrm{level}\,v = R_h \otimes_{R_D} \mathcal{G}^D.\mathrm{level}\,v, \qquad v \in \mathbb{N},$$
--   such that:
--
--   first, the $e_v$ are compatible with the transition maps: for every $v$, the transition map of $\mathcal{G}^D.\mathrm{baseChange}\,R_h$ at level $v$ precomposed with $e_{v+1}$ equals $e_v$ precomposed with the transition map of $\mathcal{G}$ at level $v$;
--
--   second, for every $v$ and every $\overline{\mathbb{Q}}$-point $x$ of $\mathcal{G}$ at level $v$ there is a $\overline{\mathbb{Q}}$-point $y$ of $\mathcal{G}^D$ at level $v$ such that for all $b \in \mathcal{G}^D.\mathrm{level}\,v$ one has $\mathrm{toAlgHom}(y)(b) = \mathrm{toAlgHom}(x)\big(e_v^{-1}(1 \otimes b)\big)$, and such that $\Delta$ of the class of $x$ equals $\Delta^D$ of the class of $y$ in $J_H(M)$.
--
--   This is the descent step identifying the finite part of the $p$-power torsion of the Néron object of $J_H(M)$ over a henselian place ring with the base change of its counterpart over the decomposition ring, both as a $p$-divisible group and through the dictionaries of $\overline{\mathbb{Q}}$-points. It is used by [`ModularCurve.exists_pDivisibleGroup_raynaudQuotient_toricPts_and_exists_retraction_finitePart_jHNeronObjectAtP_of_closedImmersion`](thm.html#ModularCurve.exists_pDivisibleGroup_raynaudQuotient_toricPts_and_exists_retraction_finitePart_jHNeronObjectAtP_of_closedImmersion), where a single $p$-divisible group over the decomposition ring must be carried along with the toric quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base)

    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)

    [Algebra ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) Rh]
    [IsScalarTower ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) Rh (AlgebraicClosure ℚ)]

    [IsDiscreteValuationRing ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)]

    (𝒢D : PDivisibleGroup ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) p h)
    (ΔD : 𝒢D.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔDinj : Function.Injective ΔD)
    (hΔDlev : ∀ (v : ℕ) (x : ModularCurve.JH M H),
      (∃ y : 𝒢D.Point (AlgebraicClosure ℚ) v, ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = x) ↔ x ∈ O.finPts (p ^ v))
    (hΔDgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → ∀ z : 𝒢D.Points (AlgebraicClosure ℚ), ΔD (τ' • z) = τ • ΔD z)
    (htorD : ∀ v : ℕ, O.toricPts (p ^ v) ≤ O.finPts (p ^ v))

    (ρD : ModularCurve.XHDRLevel.R p →+* (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)))
    (ιD : ∀ v : ℕ, Spec (CommRingCat.of (𝒢D.level v)) ⟶ O.G)
    (hρD : (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (AlgebraicClosure ℚ)).comp ρD = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιDbase : ∀ v : ℕ, ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD))
    (hιDcl : ∀ (v : ℕ) (h1 : ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρD)) (ιD v)
        (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v)))) h1))
    (hιDp : ∀ v : ℕ, ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιDmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B] (x y : 𝒢D.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιDt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢D.transition v : 𝒢D.level (v + 1) →+* 𝒢D.level v)) ≫ ιD (v + 1) = ιD v)
    (hιDfin : ∀ (v : ℕ)
      (h3 : ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρD))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρD))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρD))).base x = IsLocalRing.closedPoint (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) →
          x ∈ Set.range jv.base)

    (hιDpts : ∀ (v : ℕ) (x : 𝒢D.Point (AlgebraicClosure ℚ) v),
      (O.pts (ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] (AlgebraicClosure ℚ)) : 𝒢D.level v →+* (AlgebraicClosure ℚ))) ≫ ιD v)
    :
    ∃ e : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] (𝒢D.baseChange Rh).level v,

      (∀ v : ℕ, ((𝒢D.baseChange Rh).transition v).comp (e (v + 1) : 𝒢.level (v + 1) →ₐc[Rh] (𝒢D.baseChange Rh).level (v + 1)) =
        (e v : 𝒢.level v →ₐc[Rh] (𝒢D.baseChange Rh).level v).comp (𝒢.transition v)) ∧

      (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v), ∃ y : 𝒢D.Point (AlgebraicClosure ℚ) v,
        (∀ b : 𝒢D.level v, PDivisibleGroup.Point.toAlgHom y b =
          PDivisibleGroup.Point.toAlgHom x ((e v).symm ((1 : Rh) ⊗ₜ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] b))) ∧
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y))) := by sorry
