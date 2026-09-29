-- Prove2me | Theorems.Thm_ModularCurve_exists_pDivisibleGroup_points_eq_finPts_raynaudExtension_closedImmersion_jHNeronObjectAtP_of_representsRelSubPic
-- name    : ModularCurve.exists_pDivisibleGroup_points_eq_finPts_raynaudExtension_closedImmersion_jHNeronObjectAtP_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/63325472-b006-592f-a1b4-b7f0442da886
-- title:
--   p-divisible finite part of the Néron object for J_H(M)
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and the divisibility hypotheses `hpM` : $p \mid M$ and `hpM2` : $p^{2} \nmid M$, together with `hHp`, which requires that every unit $u$ of $\mathbb{Z}/M$ whose image under `ZMod.unitsMap` along $M/p \mid M$ is trivial already lies in $H$ (and $M/p \neq 0$).
--
--   The arithmetic data are: a valuation subring $\mathrm{Pl}$ of $\overline{\mathbb{Q}}$ with `hPl` : `Pl.LiesOverPrime p`, i.e. $p$ lies in the nonunits of $\mathrm{Pl}$, whose residue field is of characteristic $p$ and algebraically closed; the hypothesis `hj` that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤` of full level; a model $\mathfrak{X}$ of type [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81) (Deligne–Rapoport data for the two-chart integral models over the ring `R p` at the levels `ΓM M H` and `ΓN p M H hpM`, with a curve model for the geometric function field `xHFunctionFieldBar M H`, its properness, flatness, normality and smoothness clauses, and the pinning and Galois-compatibility clauses of that structure); level data $\Lambda$ of type [`ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl`](def/ModularCurve_JHNeronObjectAtP.html#L32), consisting of a section $\sigma_A$ of the base, a scheme $\Lambda.X$ with structure morphism $\Lambda.f$ to `base p`, a relative group law $\Lambda.L$ on it, and identifications of its generic and special sections with the relevant $\mathrm{Pic}^{0}$-groups; and an object $O$ of type [`ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ`](def/ModularCurve_JHNeronObjectAtP.html#L53), that is, a smooth separated surjective group scheme $O.g : O.G \to$ `base p` of locally finite type with connected fibres, carrying a commutative relative group law $O.L$, an additive identification $O.\mathrm{pts}$ of $J_H(M) = \mathrm{Pic}^{0}(\overline{\mathbb{Q}}, \mathtt{xHFunctionFieldBar } M\,H)$ with the sections of $O.g$ over the generic point, Galois compatibility, Hecke endomorphisms $O.\mathrm{hecke}\,S\,g$ compatible with the group law and with the operators `genOpH M H S g`, flatness and surjectivity of the multiplication morphisms $O.L.\mathrm{schemeNsmul}\,n$, properness of the generic fibre, a toric rank $O.\mathrm{toricRank}$ and the remaining clauses of that structure.
--
--   Two representability hypotheses are imposed. `hrep` asserts that the designation $(O.G, O.g, \text{unit section of } O.L)$ represents, in the sense of `RepresentsRelSubPic`, the subfunctor of the relative Picard functor of the structure morphism `toBase p (ΓM M H) hj` rigidified along $\mathfrak{X}.\varepsilon_{\mathrm{inf}}$ which is cut out by the condition `algEquivZeroCut`, namely fibrewise algebraic equivalence to zero of the rigidified line bundle over all algebraically closed fields; thus there is a Poincaré rigidified bundle satisfying the condition, universal for rigidified bundles satisfying it, and trivial along the zero section. `hrepΛ` asserts the same for the designation $(\Lambda.X, \Lambda.f, \text{unit section of } \Lambda.L)$ with respect to `toBase p (XHDRLevel.ΓN p M H hpM) hj` rigidified along the composite `schemeHomOverComp 𝔛.εinf 𝔛.π`.
--
--   Finally, $R_h$ is a henselian local domain which is an algebra over which $\overline{\mathbb{Q}}$ is faithful, subject to `hRA`, that the image of $R_h$ in $\overline{\mathbb{Q}}$ lies in $\mathrm{Pl}$, and `hRloc`, that an element of $R_h$ lies in the maximal ideal exactly when the $\mathrm{Pl}$-valuation of its image is $<1$; so $R_h \to \mathrm{Pl}$ is a local homomorphism.
--
--   The conclusion produces a single witness. There exist a natural number $h$, a $p$-divisible group $\mathcal{G}$ of height $h$ over $R_h$ (a tower of finite free cocommutative $R_h$-Hopf algebras $\mathcal{G}.\mathrm{level}\,v$ of rank $p^{vh}$, with surjective transition maps whose kernels are the $p^{v}$-torsion ideals), an additive map $\Delta : \mathcal{G}.\mathrm{Points}(\overline{\mathbb{Q}}) \to J_H(M)$ and a $\mathbb{Z}_p$-linear map $e$ from [`TateModule p (𝒢.Points (AlgebraicClosure ℚ))`](def/EllipticCurve_TateModule.html#L15) to [`TateModule p (JH M H)`](def/EllipticCurve_TateModule.html#L15), where [`TateModule p N`](def/EllipticCurve_TateModule.html#L15) denotes the group of sequences $(x_n)$ in $N$ with $p^{n}x_n = 0$ and $p\,x_{n+1} = x_n$, such that all of the following hold.
--
--   (i) $\Delta$ is injective.
--
--   (ii) For every $v$ and every $y \in J_H(M)$: $y$ lies in $O.\mathrm{finPts}(p^{v})$ — the subgroup generated by those $p^{v}$-torsion classes of $\mathrm{Pic}^{0}$ whose section $O.\mathrm{pts}$ satisfies the predicate `ExtendsToPlace` for $\mathrm{Pl}$ and $\Lambda.\sigma_A$ — if and only if $y = \Delta(\mathcal{G}.\mathrm{pointsMkAdd}\,v\,x)$ for some $\overline{\mathbb{Q}}$-point $x$ of $\mathcal{G}$ at level $v$, a point being an $R_h$-algebra map $\mathcal{G}.\mathrm{level}\,v \to \overline{\mathbb{Q}}$ under convolution.
--
--   (iii) Galois equivariance: for $\tau \in \mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ and $\tau'$ an $R_h$-algebra automorphism of $\overline{\mathbb{Q}}$ with $\tau' x = \tau x$ for all $x$, one has $\Delta(\tau' \cdot z) = \tau \cdot \Delta z$ for all $z$.
--
--   (iv) Hecke equivariance on points: for every set $S \subseteq \mathbb{N}$ and every generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (a $T_\ell$ for $\ell$ prime with $\ell \notin S$ and $\ell \nmid M$, a $U_q$ for $q$ prime dividing $M$, or a diamond $\langle d\rangle$) there is a family $\varphi_v$ of $R_h$-algebra and coalgebra endomorphisms of the levels commuting with the transition maps, such that precomposition of a level-$v$ point with $\varphi_v$ corresponds under $\Delta$ to the operator `genOpH M H S g` on $J_H(M)$.
--
--   (v) Tate-module packaging: $e$ is given coordinatewise by $\Delta$; $e$ is injective; a $y$ in the Tate module of $J_H(M)$ lies in the range of $e$ precisely when $y_n \in O.\mathrm{finPts}(p^{n})$ for every $n$; and $e$ intertwines $\mathcal{G}.\mathrm{tateModuleRep}$ at $\tau'$ with `JH.tateGaloisRep M H p` at $\tau$, for $\tau'$ and $\tau$ agreeing as above.
--
--   (vi) The range of $e$ is saturated: $p\cdot y \in \operatorname{range} e$ implies $y \in \operatorname{range} e$; and the quotient [`TateModule p (JH M H) ⧸ LinearMap.range e`](def/EllipticCurve_TateModule.html#L15) is $\mathbb{Z}_p$-linearly isomorphic to $\mathbb{Z}_p^{O.\mathrm{toricRank}}$.
--
--   (vii) For every $v$, each $y \in O.\mathrm{toricPts}(p^{v})$ — the subgroup generated by the range of $O.\mathrm{toricPoint}(p^{v})$ — is $\Delta$ of a level-$v$ point.
--
--   (viii) Raynaud quotient block: there exist $h_B$, a $p$-divisible group $\mathcal{B}$ of height $h_B$ over $R_h$, a family $\psi_v : \mathcal{B}.\mathrm{level}\,v \to \mathcal{G}.\mathrm{level}\,v$ of $R_h$-algebra and coalgebra maps, and $h'$, with $h = O.\mathrm{toricRank} + h_B$ and $h_B = 2h'$, such that: $\psi$ commutes with the transition maps of $\mathcal{B}$ and $\mathcal{G}$; for every $v$ and every $\overline{\mathbb{Q}}$-point $x$ of $\mathcal{G}$ at level $v$, the point $x \circ \psi_v$ of $\mathcal{B}$ is trivial if and only if $\Delta$ of $x$ lies in $O.\mathrm{toricPts}(p^{v})$; every $\overline{\mathbb{Q}}$-point $b$ of $\mathcal{B}$ at level $v$ is of the form $x \circ \psi_v$; if $x \circ \psi_v$ reduces to the identity, in the sense that $\mathrm{Pl}$-valuation of $(x\circ\psi_v)(a)$ minus the image of the counit of $a$ is $<1$ for all $a \in \mathcal{B}.\mathrm{level}\,v$, then the same estimate holds for $x$ on all of $\mathcal{G}.\mathrm{level}\,v$; and, for every $v$, every $\sigma$ in the inertia subgroup `Pl.inertiaSubgroupIn ℚ`, every $z$ in the $p^{v}$-torsion of $\mathrm{Pic}^{0}(\overline{\mathbb{Q}}, \mathtt{xHFunctionFieldBar } M\,H)$ and every level-$v$ point $y$ with $\Delta(y) = \sigma\cdot z - z$, the point $y \circ \psi_v$ of $\mathcal{B}$ reduces to the identity in the above sense.
--
--   (ix) Scheme-level block: there exist a ring homomorphism $\rho_h : \mathtt{R } p \to R_h$ and morphisms $\iota_v : \operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v) \to O.G$ with the following properties. The structure map of $R_h$ into $\overline{\mathbb{Q}}$ precomposed with $\rho_h$ is the structure map of `R p` into $\overline{\mathbb{Q}}$. Each $\iota_v$ followed by $O.g$ equals $\operatorname{Spec}$ of $R_h \to \mathcal{G}.\mathrm{level}\,v$ followed by $\operatorname{Spec} \rho_h$; and, for any witness of this identity, the induced morphism of $\operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v)$ into the fibre product of $O.g$ and $\operatorname{Spec}\rho_h$ is a closed immersion. Each $\iota_v$ followed by the multiplication $O.L.\mathrm{schemeNsmul}(p^{v})$ equals $\iota_v$ followed by $O.g$ followed by the unit section of $O.L$. For each $v$ and each $\overline{\mathbb{Q}}$-point $x$ at level $v$, the section $O.\mathrm{pts}(\Delta(x))$ is $\operatorname{Spec}$ of the algebra map underlying $x$ followed by $\iota_v$. Additivity: for every commutative $R_h$-algebra $B$, every pair $x, y$ of level-$v$ $B$-points, and witnesses $h_x, h_y$ that the corresponding morphisms lie over $\operatorname{Spec}\rho_h$, the morphism attached to $x\cdot y$ equals the product of the two sections under the relative group law $O.L$. Compatibility with transitions: $\operatorname{Spec}$ of $\mathcal{G}.\mathrm{transition}\,v$ followed by $\iota_{v+1}$ equals $\iota_v$. Hecke compatibility at scheme level: for every $S$ and $g$ as in (iv) there is a family $\varphi_v$ of $R_h$-algebra and coalgebra endomorphisms commuting with the transitions, such that $\operatorname{Spec}\varphi_v$ followed by $\iota_v$ equals $\iota_v$ followed by $O.\mathrm{hecke}\,S\,g$, and such that the corresponding action on points matches `genOpH M H S g` through $\Delta$. Lastly, for every $v$ and given witnesses $h_3$ and $h_4$ of the stated commutativities, the canonical morphism $j_v$ from $\operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v)$ into the base change along $\operatorname{Spec}\rho_h$ of the kernel of $O.L.\mathrm{schemeNsmul}(p^{v})$ (the fibre product of that multiplication morphism with the unit section) is simultaneously an open immersion and a closed immersion, and every point of that base-changed kernel whose image under the projection to $\operatorname{Spec} R_h$ is the closed point lies in the topological range of $j_v$.
--
--   This is the single-witness packaging of the finite part at $p$ of the Néron object of $J_H(M)$ in the Deligne–Rapoport setting with $p \parallel M$: one $p$-divisible group $\mathcal{G}$ over the henselian base simultaneously carries the level-by-level identification with the finite points, the Galois and Hecke equivariance and the Tate-module comparison, the Raynaud quotient $\mathcal{B}$ separating the toric part, and the realisation of $\mathcal{G}$ inside the $p^{v}$-torsion of $O.G$ as an open and closed piece meeting the special fibre. Downstream statements on the orders of the toric and finite parts, on the vanishing of the Weil pairing on toric classes, and on the action of $U_p$ and the diamond operators on the Tate module of $J_H(M)$ in the ordinary case all instantiate on this common witness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pDivisibleGroup_points_eq_finPts_raynaudExtension_closedImmersion_jHNeronObjectAtP_of_representsRelSubPic.lean

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

theorem ModularCurve.exists_pDivisibleGroup_points_eq_finPts_raynaudExtension_closedImmersion_jHNeronObjectAtP_of_representsRelSubPic
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
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1) :
    ∃ (h : ℕ) (𝒢 : PDivisibleGroup Rh p h)
      (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
      (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H)),

      Function.Injective Δ ∧

      (∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
        ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y) ∧

      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
        (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
        ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z) ∧

      (∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
        (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
        ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) ∧

      (∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
        ((e x : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n =
          Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n)) ∧
      Function.Injective e ∧
      (∀ y : TateModule p (ModularCurve.JH M H), y ∈ LinearMap.range e ↔
        ∀ n : ℕ, (y : ℕ → ModularCurve.JH M H) n ∈ O.finPts (p ^ n)) ∧
      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
        (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
        ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
          e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) = ModularCurve.JH.tateGaloisRep M H p τ (e x)) ∧

      (∀ y : TateModule p (ModularCurve.JH M H), (p : ℤ_[p]) • y ∈ LinearMap.range e → y ∈ LinearMap.range e) ∧
      Nonempty ((TateModule p (ModularCurve.JH M H) ⧸ LinearMap.range e) ≃ₗ[ℤ_[p]] (Fin O.toricRank → ℤ_[p])) ∧

      (∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
        ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y) ∧

      ∃ (hB : ℕ) (ℬ : PDivisibleGroup Rh p hB) (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v) (h' : ℕ),

        h = O.toricRank + hB ∧ hB = 2 * h' ∧

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

        (∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
          ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
          ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
            Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
            (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
              algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)) ∧

      ∃ (ρh : ModularCurve.XHDRLevel.R p →+* Rh) (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G),

        (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ) ∧

        (∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)) ∧

        (∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
          IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
            (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1)) ∧

        (∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ∧

        (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
            Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v) ∧

        (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
          (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
          (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
            (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧

        (∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v) ∧

        (∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
          (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
          (∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1) ∧
          ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
            Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
              ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) ∧

        (∀ (v : ℕ)
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
              x ∈ Set.range jv.base) := by sorry
