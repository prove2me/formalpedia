-- Prove2me | Theorems.Thm_ModularCurve_exists_pDivisibleGroup_raynaudQuotient_toricPts_and_exists_retraction_finitePart_jHNeronObjectAtP_of_closedImmersion
-- name    : ModularCurve.exists_pDivisibleGroup_raynaudQuotient_toricPts_and_exists_retraction_finitePart_jHNeronObjectAtP_of_closedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/197c7cb8-b071-57e1-b296-4de44c6e541f
-- title:
--   Split Raynaud quotient of the finite part by toric points
-- statement:
--   Throughout, $p$ is a prime and $M$ a non-zero natural number, $H$ a subgroup of $(\mathbb{Z}/M)^{\times}$, and the arithmetic data consists of: $p \mid M$ (`hpM`), $p^{2} \nmid M$ (`hpM2`), and the hypothesis `hHp` that every unit of $\mathbb{Z}/M$ mapping to $1$ under reduction to $(\mathbb{Z}/(M/p))^{\times}$ lies in $H$, together with $M/p \neq 0$.
--
--   The place data consists of a valuation subring $Pl$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `Pl.LiesOverPrime p`, that is, $p$ is a non-unit of $Pl$, whose residue field is of characteristic $p$ and algebraically closed.
--
--   The model and Néron data consists of: the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the function field `qExpFunctionFieldC ℚ ⊤` of the full modular group; an integral model $\mathfrak{X}$ of type [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81) for the curves of levels $\Gamma_M$ and $\Gamma_N$ over the ring $R_p$ of rationals with denominator prime to $p$; level data $\Lambda$ (a scheme $\Lambda.X$ over the base with a relative group law $\Lambda.L$ and dictionaries of points at the generic and the special fibre) and an object $O$ of type [`ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ`](def/ModularCurve_JHNeronObjectAtP.html#L53), so $O.G$ is a smooth separated surjective group scheme $O.g : O.G \to$ `base p` with commutative relative group law $O.L$, a bijection $O.\mathrm{pts}$ between $J_H = \mathrm{Pic}^{0}(\overline{\mathbb{Q}}, \,$`xHFunctionFieldBar M H`$)$ and the generic-fibre sections, Hecke operators, and in particular a natural number $O.\mathrm{toricRank}$.
--
--   The representability hypotheses are `hrep` and `hrepΛ`: the Picard subfunctor condition `algEquivZeroCut` (rigidified line bundles that are fibrewise algebraically equivalent to zero) on the model of level $\Gamma_M$, rigidified along the section $\mathfrak{X}.\varepsilon_{\inf}$, is represented by the designation with underlying scheme $O.G$, structure morphism $O.g$ and zero section the unit of $O.L$; and likewise the corresponding condition on the model of level $\Gamma_N$, rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$, is represented by $(\Lambda.X, \Lambda.f)$ with zero section the unit of $\Lambda.L$. Both are asserted only as non-emptiness of the corresponding representability structure.
--
--   The henselian base consists of a henselian local domain $R_h$ which is an algebra over which $\overline{\mathbb{Q}}$ is faithful, such that every element of $R_h$ maps into $Pl$ (`hRA`) and the maximal ideal of $R_h$ is exactly the set of elements whose image has $Pl$-valuation $< 1$ (`hRloc`).
--
--   The finite part consists of a $p$-divisible group $\mathcal{G}$ over $R_h$ of height $h$ (levels $\mathcal{G}.\mathrm{level}\,v$, finite free cocommutative Hopf $R_h$-algebras of rank $p^{vh}$ with surjective transition maps whose kernels are the $p^{v}$-torsion ideals), a ring homomorphism $\rho_h : R_p \to R_h$, and morphisms $\iota_v : \operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v) \to O.G$, subject to: `hρh`, compatibility of $\rho_h$ with the structure maps to $\overline{\mathbb{Q}}$; `hιbase`, that $\iota_v$ followed by $O.g$ is $\operatorname{Spec}$ of the structure map $R_h \to \mathcal{G}.\mathrm{level}\,v$ followed by $\operatorname{Spec} \rho_h$; `hιcl`, that for each such identity the induced morphism to the fibre product of $O.g$ and $\operatorname{Spec} \rho_h$ is a closed immersion; `hιp`, that $\iota_v$ followed by multiplication by $p^{v}$ for $O.L$ factors through the unit section; `hιmul`, that for every $v$, every commutative $R_h$-algebra $B$ and all level-$v$ points $x,y$ with values in $B$ satisfying the stated compatibilities over the base, the morphism attached to $x \cdot y$ composed with $\iota_v$ equals the $O.L$-product of the corresponding sections; `hιt`, that $\operatorname{Spec}$ of the transition map followed by $\iota_{v+1}$ equals $\iota_v$; and `hιfin`, which states for each $v$ (given the two compatibility identities `h3`, `h4`) that the canonical morphism $j_v$ from $\operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v)$ into the fibre product of the $p^{v}$-kernel of $O.L$ with $\operatorname{Spec} \rho_h$ is both an open and a closed immersion, and that every point of that fibre product lying over the closed point of $R_h$ lies in the image of $j_v$.
--
--   The points dictionary consists of an additive map $\Delta$ from $\mathcal{G}.\mathrm{Points}(\overline{\mathbb{Q}})$ (the direct limit of the level-wise point groups, written additively) to $J_H$, subject to: `hΔinj`, injectivity; `hΔlev`, that for each $v$ an element $y \in J_H$ lies in $O.\mathrm{finPts}(p^{v})$ — the subgroup generated by the $p^{v}$-torsion classes of $\mathrm{Pic}^{0}$ whose section $O.\mathrm{pts}$ extends over the place — if and only if $y = \Delta(x)$ for some level-$v$ point $x$ with values in $\overline{\mathbb{Q}}$; `hΔgal`, that $\Delta$ is equivariant for $\tau \in \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ and any $R_h$-algebra automorphism $\tau'$ of $\overline{\mathbb{Q}}$ agreeing with $\tau$ pointwise; `htor`, that every element of $O.\mathrm{toricPts}(p^{v})$ (the subgroup generated by the range of $O.\mathrm{toricPoint}$ at $p^{v}$) comes from a level-$v$ point via $\Delta$; and `hιpts`, that the section $O.\mathrm{pts}(\Delta(x))$ is given by $\operatorname{Spec}$ of the algebra homomorphism underlying $x$ followed by $\iota_v$.
--
--   Under these hypotheses there exist a natural number $h_B$, a $p$-divisible group $\mathcal{B}$ over $R_h$ of height $h_B$, bialgebra homomorphisms $\psi_v : \mathcal{B}.\mathrm{level}\,v \to \mathcal{G}.\mathrm{level}\,v$ over $R_h$ for all $v$, and a natural number $h'$, such that:
--
--   1. $h = O.\mathrm{toricRank} + h_B$;
--
--   2. $h_B = 2h'$;
--
--   3. for every $v$, $\mathcal{G}.\mathrm{transition}_v \circ \psi_{v+1} = \psi_v \circ \mathcal{B}.\mathrm{transition}_v$;
--
--   4. for every $v$ and every level-$v$ point $x$ of $\mathcal{G}$ with values in $\overline{\mathbb{Q}}$, the point of $\mathcal{B}$ obtained by composing the algebra homomorphism of $x$ with $\psi_v$ is the identity element of $\mathcal{B}.\mathrm{Point}(\overline{\mathbb{Q}})_v$ if and only if $\Delta(x) \in O.\mathrm{toricPts}(p^{v})$;
--
--   5. for every $v$ and every $b \in \mathcal{B}.\mathrm{Point}(\overline{\mathbb{Q}})_v$ there is a level-$v$ point $x$ of $\mathcal{G}$ whose composite with $\psi_v$ is $b$;
--
--   6. for every $v$ and every level-$v$ point $x$ of $\mathcal{G}$: if for all $a \in \mathcal{B}.\mathrm{level}\,v$ the $Pl$-valuation of the composite point evaluated at $a$ minus the image of the counit of $a$ is $< 1$, then for all $a \in \mathcal{G}.\mathrm{level}\,v$ the $Pl$-valuation of $x(a)$ minus the image of the counit of $a$ is $< 1$;
--
--   7. for every $v$ there is an $R_h$-linear map $r : \mathcal{G}.\mathrm{level}\,v \to \mathcal{B}.\mathrm{level}\,v$ with $r(\psi_v(b)) = b$ for all $b \in \mathcal{B}.\mathrm{level}\,v$.
--
--   Injectivity of the $\psi_v$ is not asserted separately; it follows from the last conjunct.
--
--   This is the construction of the quotient of the finite ($p$-divisible) part of the Néron object of $J_H$ at $p$ by the $p$-divisible subgroup generated by the toric points: the quotient $\mathcal{B}$ has even height $h_B = h - O.\mathrm{toricRank}$, its $\overline{\mathbb{Q}}$-points are exactly the points of $\mathcal{G}$ modulo the toric ones, it detects reduction to the identity at the place, and each level of $\mathcal{B}$ is an $R_h$-module direct summand of the corresponding level of $\mathcal{G}$. It feeds the analysis of the $p$-adic Galois module attached to $J_H$ at the prime $p$ used in the level-lowering step, and is cited in the further study of the Raynaud quotient and of the finite part of $J_H$ over a discrete valuation base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pDivisibleGroup_raynaudQuotient_toricPts_and_exists_retraction_finitePart_jHNeronObjectAtP_of_closedImmersion.lean

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

theorem ModularCurve.exists_pDivisibleGroup_raynaudQuotient_toricPts_and_exists_retraction_finitePart_jHNeronObjectAtP_of_closedImmersion
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
    :
    ∃ (hB : ℕ) (ℬ : PDivisibleGroup Rh p hB) (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v) (h' : ℕ),
      h = O.toricRank + hB ∧
      hB = 2 * h' ∧
      (∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v)) ∧
      (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v)) ∧
      (∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) = b) ∧
      (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)) ∧

      (∀ v : ℕ, ∃ r : 𝒢.level v →ₗ[Rh] ℬ.level v, ∀ b : ℬ.level v, r (ψ v b) = b) := by sorry
