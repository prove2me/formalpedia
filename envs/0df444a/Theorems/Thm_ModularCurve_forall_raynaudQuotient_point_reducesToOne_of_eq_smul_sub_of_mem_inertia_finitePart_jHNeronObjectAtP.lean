-- Prove2me | Theorems.Thm_ModularCurve_forall_raynaudQuotient_point_reducesToOne_of_eq_smul_sub_of_mem_inertia_finitePart_jHNeronObjectAtP
-- name    : ModularCurve.forall_raynaudQuotient_point_reducesToOne_of_eq_smul_sub_of_mem_inertia_finitePart_jHNeronObjectAtP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/dce42505-11c3-5540-a5c4-56dd5201f95d
-- title:
--   Inertia displacements reduce to one on the Raynaud quotient
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer divisible by $p$ but not by $p^2$ (`hpM`, `hpM2`), $H$ is a subgroup of $(\mathbb{Z}/M)^\times$ with the property `hHp` that every unit of $\mathbb{Z}/M$ whose image under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial already lies in $H$, and $M/p$ is nonzero. Further, $Pl$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $p$ a non-unit of $Pl$ (`hPl`, i.e. `Pl.LiesOverPrime p`), whose residue field is algebraically closed of characteristic $p$; and `hj` asserts that the $q$-expansion `jqModC ℚ` of the modular invariant lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb{Q}$ by the ratios of integral forms of level $\mathrm{SL}_2(\mathbb{Z})$.
--
--   The geometric input consists of: an integral model datum $\mathfrak{X}$ of type [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81) for the modular curves of level $\Gamma_M(H)$ and $\Gamma_N$ over the subring $R(p) \subset \mathbb{Q}$ of rationals with denominator prime to $p$; a level datum $\Lambda$ and a Néron object $O$ for $J_H(M) = \operatorname{Pic}^0_{\overline{\mathbb{Q}}}$ of the function field `xHFunctionFieldBar M H`, in the sense of [`ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ`](def/ModularCurve_JHNeronObjectAtP.html#L53); and two representability hypotheses. The first, `hrep`, provides an element of `RepresentsRelSubPic`, that is, a Poincaré rigidified line bundle exhibiting the designation $(O.G, O.g)$ with the unit section of the relative group law $O.L$ as zero section, as representing the subfunctor of the relative Picard functor of `toBase p (ΓM M H) hj`, rigidified along $\mathfrak{X}.\varepsilon_{\inf}$, cut out by the condition `algEquivZeroCut` (fibrewise algebraic equivalence to zero over algebraically closed residue fields). The second, `hrepΛ`, is the analogous datum for the level-$\Gamma_N$ model `toBase p (ΓN p M H hpM) hj`, rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$, with the designation $(\Lambda.X, \Lambda.f)$ and the unit section of $\Lambda.L$.
--
--   Next, $Rh$ is a henselian local domain, given as an algebra over which $\overline{\mathbb{Q}}$ is a faithful module, such that every element of $Rh$ maps into $Pl$ (`hRA`) and such that an element of $Rh$ lies in the maximal ideal exactly when the $Pl$-valuation of its image is $<1$ (`hRloc`).
--
--   The finite-part data consist of a $p$-divisible group $\mathcal{G}$ over $Rh$ of height $h$ — a system of finite free $Rh$-Hopf algebras `𝒢.level v` of rank $p^{vh}$ with surjective transition maps whose kernels are the $p^v$-torsion ideals — a ring homomorphism $\rho_h \colon R(p) \to Rh$, and morphisms $\iota_v \colon \operatorname{Spec}(\mathcal{G}.\mathrm{level}\, v) \to O.G$, subject to: `hρh`, the compatibility $\operatorname{alg}_{Rh} \circ \rho_h = \operatorname{alg}_{R(p)}$ of structure maps to $\overline{\mathbb{Q}}$; `hιbase`, that $\iota_v$ followed by $O.g$ equals $\operatorname{Spec}$ of $Rh \to \mathcal{G}.\mathrm{level}\, v$ followed by $\operatorname{Spec}\rho_h$; `hιcl`, that the resulting morphism from $\operatorname{Spec}(\mathcal{G}.\mathrm{level}\, v)$ into the fibre product of $O.g$ with $\operatorname{Spec}\rho_h$ is a closed immersion; `hιp`, that $\iota_v$ followed by the multiplication-by-$p^v$ endomorphism `O.L.schemeNsmul (p ^ v)` agrees with $\iota_v$ followed by $O.g$ and then the unit section; `hιmul`, that for every $v$, every commutative $Rh$-algebra $B$ and all level-$v$ points $x, y$ of $\mathcal{G}$ with values in $B$ whose composites with $\iota_v$ lie over the base (hypotheses `hx`, `hy`), the point $xy$ composed with $\iota_v$ equals the product of the two resulting sections under $O.L.\mathrm{mul}$; `hιt`, that $\operatorname{Spec}$ of the transition map $\mathcal{G}.\mathrm{level}(v+1) \to \mathcal{G}.\mathrm{level}\, v$ followed by $\iota_{v+1}$ equals $\iota_v$; and `hιfin`, the open-and-closed finite-part clause: for each $v$, given the equalities `h3`, `h4` expressing that $\iota_v$ factors through the kernel of multiplication by $p^v$ over the base, the induced morphism $j_v$ from $\operatorname{Spec}(\mathcal{G}.\mathrm{level}\, v)$ to the base change to $\operatorname{Spec} Rh$ of that kernel is an open immersion, is a closed immersion, and every point of that base change whose image in $\operatorname{Spec} Rh$ is the closed point lies in the range of $j_v$ on points.
--
--   The points dictionary is an additive map $\Delta$ from the direct limit $\mathcal{G}.\mathrm{Points}(\overline{\mathbb{Q}})$ of the level groups to $J_H(M)$, subject to: `hΔinj`, injectivity; `hΔlev`, that for each $v$ an element $y \in J_H(M)$ lies in $O.\mathrm{finPts}(p^v)$ — the subgroup generated by the $p^v$-torsion classes $x$ of $\operatorname{Pic}^0$ whose section $O.\mathrm{pts}\, x$ satisfies the predicate `ExtendsToPlace Pl Λ.σA` — if and only if $y = \Delta(x)$ for some level-$v$ point $x$ of $\mathcal{G}$ over $\overline{\mathbb{Q}}$, transported into the limit by `𝒢.pointsMkAdd`; `hΔgal`, that $\Delta(\tau' \cdot z) = \tau \cdot \Delta z$ whenever $\tau$ is an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ and $\tau'$ an automorphism over $Rh$ with the same underlying map; `htor`, that every element of $O.\mathrm{toricPts}(p^v)$ — the subgroup generated by the image of `O.toricPoint (p ^ v)` — is of the form $\Delta(x)$ for a level-$v$ point $x$; and `hιpts`, that the section $O.\mathrm{pts}(\Delta(x))$ attached to such a point is $\operatorname{Spec}$ of the $Rh$-algebra map underlying $x$ followed by $\iota_v$.
--
--   Finally, the quotient data consist of a $p$-divisible group $\mathcal{B}$ over $Rh$ of height $h_B$ together with coalgebra-and-algebra maps $\psi_v \colon \mathcal{B}.\mathrm{level}\, v \to \mathcal{G}.\mathrm{level}\, v$, subject to: `hψt`, compatibility with the transition maps, $\mathcal{G}.\mathrm{transition}_v \circ \psi_{v+1} = \psi_v \circ \mathcal{B}.\mathrm{transition}_v$; `hψker`, that for every level-$v$ point $x$ of $\mathcal{G}$ over $\overline{\mathbb{Q}}$ the point $x \circ \psi_v$ of $\mathcal{B}$ is the identity point if and only if $\Delta(x) \in O.\mathrm{toricPts}(p^v)$; and `hψsurj`, that every level-$v$ point of $\mathcal{B}$ over $\overline{\mathbb{Q}}$ is of the form $x \circ \psi_v$.
--
--   Under these hypotheses the conclusion is the following. For every $v \in \mathbb{N}$, every $\sigma$ in the inertia subgroup of $Pl$ inside $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ (the image of `Pl.inertiaSubgroup` under the inclusion of the decomposition subgroup), every $z$ in the $p^v$-torsion of $\operatorname{Pic}^0_{\overline{\mathbb{Q}}}$ of `xHFunctionFieldBar M H`, and every level-$v$ point $y$ of $\mathcal{G}$ over $\overline{\mathbb{Q}}$ such that $\Delta(y) = \sigma \cdot z - z$: for all $a \in \mathcal{B}.\mathrm{level}\, v$,
--   $$\mathrm{val}_{Pl}\bigl( (y \circ \psi_v)(a) - \operatorname{alg}_{Rh \to \overline{\mathbb{Q}}}(\epsilon(a)) \bigr) < 1,$$
--   where $y \circ \psi_v$ denotes the point of $\mathcal{B}$ obtained by precomposing the $Rh$-algebra map underlying $y$ with $\psi_v$, and $\epsilon$ is the counit of $\mathcal{B}.\mathrm{level}\, v$. That is, the image in $\mathcal{B}$ of any inertia displacement $\sigma z - z$ of $p$-power torsion reduces to the identity point at $Pl$.
--
--   This is the clause, in the construction of the finite part of the Néron object of $J_H(M)$ at $p$ as a $p$-divisible group, which records that inertia at a place above $p$ moves $p$-power torsion classes only inside the toric part, so that after passage to the quotient $\mathcal{B}$ the displacements $\sigma z - z$ lie in the formal group, i.e. reduce to the identity modulo the maximal ideal. It is used by [`ModularCurve.exists_pDivisibleGroup_points_eq_finPts_raynaudExtension_closedImmersion_jHNeronObjectAtP_of_representsRelSubPic`](thm.html#ModularCurve.exists_pDivisibleGroup_points_eq_finPts_raynaudExtension_closedImmersion_jHNeronObjectAtP_of_representsRelSubPic), and rests on the separatedness of $O.g$ together with the statement that $\sigma z - z$ extends to a section over the valuation ring whose reduction is the unit section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_forall_raynaudQuotient_point_reducesToOne_of_eq_smul_sub_of_mem_inertia_finitePart_jHNeronObjectAtP.lean

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
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.forall_raynaudQuotient_point_reducesToOne_of_eq_smul_sub_of_mem_inertia_finitePart_jHNeronObjectAtP
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
    {hB : ℕ}
    (ℬ : PDivisibleGroup Rh p hB)
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v)
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) = b)
    :
      (∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
      ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
        (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)) := by sorry
