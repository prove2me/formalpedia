-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_units_forall_qc_comp_baseChange_U_comp_diamond_comp_eq_qc_comp_verschiebung_of_ordinaryIdempotent_of_bridge
-- name    : ModularCurve.JHNeronObjectAtP.exists_units_forall_qc_comp_baseChange_U_comp_diamond_comp_eq_qc_comp_verschiebung_of_ordinaryIdempotent_of_bridge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/63c0f005-591e-5caa-bb45-251d8275ce04
-- title:
--   Verschiebung equals Uₚ⟨ d₀⟩ on the connected part
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$ (hypotheses `hpM`, `hpM2`), and a subgroup $H \le (\mathbf Z/M)^\times$ which, by `hHp`, contains every unit mapping to $1$ under the reduction $(\mathbf Z/M)^\times \to (\mathbf Z/(M/p))^\times$. Fix a valuation subring $Pl$ of $\overline{\mathbf Q}$ with $p$ a non-unit of $Pl$ (`hPl`), whose residue field is of characteristic $p$ and algebraically closed, and assume `hj`, that the $q$-expansion [`ModularCurve.jqModC`](def/ModularCurve_JqCoeff.html#L15) of $j$ lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbf Z)$ over $\mathbf Q$.
--
--   The geometric input consists of: an integral model $\mathfrak X$ of the modular curve of level $\Gamma_M(M,H)$ over $R_p$ (the subring of $\mathbf Q$ of rationals with denominator coprime to $p$), in the sense of [`ModularCurve.XHDRModelAtP`](def/ModularCurve_XHDRModelAtP.html#L81); level data $\Lambda$ at level $M/p$, consisting of a section $\Lambda.\sigma A : \operatorname{Spec} Pl \to \operatorname{Spec} R_p$ lifting the generic point, a scheme $\Lambda.X$ over $\operatorname{Spec} R_p$ with a relative group law $\Lambda.L$, and bijections $\Lambda.\mathrm{pts}$, $\Lambda.\mathrm{ptsSp}$ between $J_H(M/p)$, respectively the degree-zero Picard group of the residue-field function field, and the sets of sections of $\Lambda.f$ over the generic, respectively the residual, point; and a Néron object $O$ at level $H$ over $\Lambda$, with group scheme $O.G \to \operatorname{Spec} R_p$, relative group law $O.L$, identification $O.\mathrm{pts} : J_H(M) \simeq$ sections over the generic point, Hecke sections $O.\mathrm{hecke}$, degeneracy maps $O.\mathrm{degPts}$, the finite-point subgroups $O.\mathrm{finPts}$, the gluing set $O.\mathrm{ssFinset}$ of pairs of places and the identification $O.\mathrm{ptsSp}$ of the glued degree-zero Picard group with the sections over the residual point. The hypothesis `hrep` asserts that $O.G$, with the unit section of $O.L$, represents the relative Picard functor of $\mathfrak X$ rigidified along $\mathfrak X.\varepsilon_{\inf}$ and cut out by the fibrewise algebraic-equivalence-zero condition.
--
--   The local base is a Henselian local domain $R^h$ with an algebra map to $\overline{\mathbf Q}$ (faithful), whose image lies in $Pl$ (`hRA`) and whose maximal ideal is exactly the locus where the valuation is $<1$ (`hRloc`), together with an algebra map $R^h \to \mathbf Z/p$ whose kernel is that same locus (`hres`). Over $R^h$ there is a $p$-divisible group $\mathcal G$ of height $h$, given by the tower of finite free cocommutative Hopf algebras $\mathcal G.\mathrm{level}\,v$ with surjective transition maps. An injective additive map $\Delta$ (hypothesis `hΔ`) carries the points of $\mathcal G$ over $\overline{\mathbf Q}$ into $J_H(M)$, and `hfin` identifies, for each $v$, the subgroup $O.\mathrm{finPts}(p^v)$ with the image under $\Delta$ of the level-$v$ points. The bridge data consist of a ring map $\rho^h : R_p \to R^h$ and morphisms $\iota_v : \operatorname{Spec}(\mathcal G.\mathrm{level}\,v) \to O.G$, subject to: `hS0` (compatibility of $\rho^h$ with the maps to $\overline{\mathbf Q}$); `hS1` (the structural square $\iota_v$ followed by $O.g$ equals $\operatorname{Spec}$ of the structure map of $\mathcal G.\mathrm{level}\,v$ followed by $\operatorname{Spec}\rho^h$); `hS2` (the induced lift into the fibre product of $O.g$ with $\operatorname{Spec}\rho^h$ is a closed immersion); `hS3` ($\iota_v$ followed by multiplication by $p^v$ on $O.G$ factors through the unit section); `hS4` (for a level-$v$ point $x$ over $\overline{\mathbf Q}$, the section $O.\mathrm{pts}(\Delta x)$ is $\operatorname{Spec}$ of the associated algebra map followed by $\iota_v$); `hS5` (for any $R^h$-algebra $B$ and level-$v$ points $x,y$ over $B$ satisfying the two structural squares, the map attached to $x \cdot y$ agrees with the $O.L$-product of those attached to $x$ and $y$); `hS6` ($\operatorname{Spec}$ of the transition map followed by $\iota_{v+1}$ equals $\iota_v$); and `hS8`, which asserts, for each $v$ and each pair of proofs of the relevant commutativities, that the canonical lift $j_v$ of the $p^v$-torsion datum into the iterated fibre product is both an open and a closed immersion, and that every point of that fibre product lying over the closed point of $R^h$ is in the image of $j_v$.
--
--   Further data: a set of primes $S$; a transition-compatible family $u_v$ of $R^h$-bialgebra endomorphisms of $\mathcal G.\mathrm{level}\,v$ (`hu`) which realises the Hecke section $O.\mathrm{hecke}\,S\,(U_p)$ along $\iota$ (`huι`); a ring map $\rho : R_p \to Pl$ compatible with the inclusion into $\overline{\mathbf Q}$ (`hρ`) with $\Lambda.\sigma A = \operatorname{Spec}\rho$ (`hσA`); the positivity assumption on $M/p$.
--
--   The reduction hypotheses are the following. `hsp`: for each $i \in \{0,1\}$, each pair of $\overline{\mathbf Q}$-points $y_1,y_2$ of $\mathfrak X.\mathrm{Meta}.C$, sections $u_1,u_2$ of $\mathfrak X$ over $\operatorname{Spec}\rho$ whose base change to $\overline{\mathbf Q}$ is $y_1$, respectively $y_2$ and whose image lies in the smooth locus, residue-field sections $u\kappa_1,u\kappa_2$ of the special fibre compatible with $u_1,u_2$ and with the structure map, closed points $P_1,P_2$ of the special-fibre curve model $\mathfrak X.\mathrm{Mfib}$ whose image under the $i$-th component map of that model is the closed point of $u\kappa_1$, respectively $u\kappa_2$, a degree-zero divisor $Dv$ equal to $[\,y_1\,] - [\,y_2\,]$ in places, and an admissible gluing datum $x$ whose first component is $[P_1]-[P_2]$ if $i=0$ and $0$ otherwise, whose second component is $[P_1]-[P_2]$ if $i=1$ and $0$ otherwise, and whose third component vanishes: then there is a section $s$ of $O.g$ over $\Lambda.\sigma A$ with $O.\mathrm{pts}$ of the class of $Dv$ equal to $s$ base-changed to $\overline{\mathbf Q}$, and with the glued class of the restriction of $s$ to the residual point equal to the class of $x$. `hspΛ` is the corresponding statement one level down, with $Q_1,Q_2$ lying over the images under $\mathfrak X.\pi$ (for $i=0$) or $\mathfrak X.\pi_w$ (for $i=1$), producing a section $s_0$ of $\Lambda.f$ whose generic value is $\Lambda.\mathrm{pts}(O.\mathrm{degPts}\,i$ of the class of $Dv)$ and whose residual value is the class of $Dw = [Q_1]-[Q_2]$. `hdia0`: for each unit $e$ of $\mathbf Z/(M/p)$ and each closed point $P$, the point obtained by transporting $P$ through the automorphism $\mathfrak X.\mathrm{dia0}\,e$ of the special fibre is again closed, and its place is the image of the place of $P$ under the semilinear automorphism given by the diamond action of the $\Gamma_0$-lift of $e$.
--
--   The Frobenius and degeneracy hypotheses are: endomorphisms $F,F^{-1},F^{*}$ of the degree-zero Picard group of the residue-field function field with $F$ the Frobenius pushforward (`hF`), $F^{-1}$ a two-sided inverse of $F$ (`hFinv`) and $F^{*} = p \cdot F^{-1}$ (`hFstar`); a unit $pb$ of $\mathbf Z/(M/p)$ reducing to $p$ (`hpb`) and the endomorphism $\delta$ given by the diamond action of its $\Gamma_0$-lift (`hδ`); maps $\alpha^{\mathrm{pull}}_i : J_H(M/p) \to J_H(M)$ and sections $\mathrm{degPull}_i$ of $O.g$ over $\Lambda.f$, for $i \in \{0,1\}$, compatible on generic points (`hpull`) and with the group laws (`hpull_mul`), and such that on the residual point (`hpullsp`) the pair of Picard components of the glued class of a section composed with $\mathrm{degPull}_i$ is $(z, F^{*}z)$ for $i=0$ and $(F^{*}z, \delta z)$ for $i=1$, where $z$ is the class corresponding to the section; an endomorphism $\bar W$ of $J_H(M)$ given by the action of a semilinear automorphism $w_{\mathrm{gen}}$ (`hWbar`) pinned by `hwgen` through the involution $\mathfrak X.w$ on points; the Eichler–Shimura-type relation `hUPgen`, that the $U_p$-operator on $J_H(M)$ plus $\bar W$ equals $\alpha^{\mathrm{pull}}_1 \circ O.\mathrm{degPts}_0$; a permutation $\sigma$ of $O.\mathrm{ssFinset}$ exchanging the components in the sense that the second component of $\sigma(n)$ is the first component of $n$ (`hσ`); a permutation $\Phi$ of the places equal to the Frobenius place map (`hΦ`), with `hFdiv` saying that $F$ sends the class of $D$ to the class of $D'$ whenever $D'$ is the $\Phi$-pushforward of $D$; and `hpull1sp`, which, for a degree-zero divisor $D$ vanishing at each place occurring in $O.\mathrm{ssFinset}$ and at its $\Phi$-image, and an admissible gluing datum $x_1$ whose first component is $p$ times the $\Phi^{-1}$-pushforward of $D$, whose second component is the $pb$-diamond translate of $D$ and whose third component vanishes, identifies the glued class of the section $\Lambda.\mathrm{ptsSp}$ of the class of $D$ composed with $\mathrm{degPull}_1$ with the class of $x_1$.
--
--   The ordinary projector data are two families $\varepsilon_v, w_v$ of $R^h$-bialgebra endomorphisms of $\mathcal G.\mathrm{level}\,v$ with: $\varepsilon_v$ idempotent (`hεε`), transition-compatible (`hεtr`), commuting with $u_v$ (`hεu`); $w_v$ transition-compatible (`hwtr`), with $\varepsilon_v \circ w_v = w_v$ (`hεw`) and $w_v \circ \varepsilon_v = w_v$ (`hwε`); and $u_v \varepsilon_v$ invertible on the $\varepsilon$-part with inverse $w_v$, in the sense $w_v \circ (u_v \circ \varepsilon_v) = \varepsilon_v$ (`hwuε`) and $(u_v \circ \varepsilon_v) \circ w_v = \varepsilon_v$ (`huεw`). A Cartier duality $\mathrm{Dual}$ between $\mathcal G$ and a second $p$-divisible group $\mathcal G'$ of the same height is given.
--
--   The connected–étale data for the special-fibre tower $B_v := \mathbf Z/p \otimes_{R^h} \mathcal G.\mathrm{level}\,v$ are: natural numbers $h^c, h^e$ with $h^c + h^e = h$ (`hsum`); towers $G^c_v$, $G^e_v$ of finite cocommutative Hopf algebras over $\mathbf Z/p$ with transition maps $s^c_v$, $s^e_v$; surjections $q^c_v : B_v \to G^c_v$ and $\pi^e_v : B_v \to G^e_v$ (`hqc`, `hπe`); a section $\sigma_v : G^e_v \to B_v$ of $\pi^e_v$ (`hπeσ`); and a map $\Theta_v : B_v \to G^c_v \otimes G^e_v$; subject to: $G^c_v$ local (`hGc`), $G^e_v$ reduced (`hGe`) and formally unramified over $\mathbf Z/p$ (`hGe'`); $s^c_v$, $s^e_v$ surjective with the prescribed ranks $p^{v h^c}$, $p^{v h^e}$ and kernels the $p^v$-torsion ideals (`hsc`, `hrankGc`, `hkerGc`, `hse`, `hrankGe`, `hkerGe`); the kernel of $\pi^e_v$ the nilradical of $B_v$ (`hkerπe`); the kernel of $q^c_v$ the ideal generated by the image under $\sigma_v$ of the augmentation ideal of $G^e_v$ (`hkerqc`); $\Theta_v$ bijective (`hΘ`) and given by $q^c_v \otimes \pi^e_v$ applied to the comultiplication (`hΘ'`); and the four transition compatibilities `hqcs`, `hπes`, `hsσ`, `hΘs` for $q^c$, $\pi^e$, $\sigma$ and $\Theta$. Finally, a family $V_{B_v}$ of $\mathbf Z/p$-bialgebra endomorphisms of $B_v$ is given with $(V_{B_v} b)^p = p \cdot b$ (`hVB1`), $V_{B_v}(b^p) = p \cdot b$ (`hVB2`), and $\varphi(V_{B_v} b) = \varphi^p(b)$ for every element $\varphi$ of the Cartier dual of $B_v$ (`hVB3`), where $p \cdot$ denotes the $p$-fold convolution power of the identity.
--
--   Under these hypotheses there exists a unit $d_0$ of $\mathbf Z/M$ with the following property. Let $\delta_v$ be any family of $R^h$-bialgebra endomorphisms of $\mathcal G.\mathrm{level}\,v$ which is transition-compatible, which realises the diamond section $O.\mathrm{hecke}\,S\,\langle d_0 \rangle$ along $\iota$ (that is, $\operatorname{Spec}\delta_v$ followed by $\iota_v$ equals $\iota_v$ followed by that section), which commutes with every $\varepsilon_v$ and which commutes with every $u_v$. Then for every $v$ the equality of $\mathbf Z/p$-algebra homomorphisms
--   $$q^c_v \circ \bigl(\mathrm{id}_{\mathbf Z/p} \otimes (u_v \circ \delta_v)\bigr) \circ \bigl(\mathrm{id}_{\mathbf Z/p} \otimes \varepsilon_v\bigr) \;=\; q^c_v \circ V_{B_v} \circ \bigl(\mathrm{id}_{\mathbf Z/p} \otimes \varepsilon_v\bigr)$$
--   holds on $B_v = \mathbf Z/p \otimes_{R^h} \mathcal G.\mathrm{level}\,v$.
--
--   This is the multiplicative Eichler–Shimura relation at a prime $p$ exactly dividing the level, expressed at the level of the Hopf algebras of the special fibre: on the connected quotient of the ordinary part, the Hecke operator $U_p$ twisted by a suitable diamond operator $\langle d_0 \rangle$ coincides with the Verschiebung. It is used in the deduction of the valuation estimate for points under the Cartier transpose of $U_p \langle d_0 \rangle$, which in turn feeds the analysis of the local behaviour at $p$ of the Galois representations attached to $J_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_units_forall_qc_comp_baseChange_U_comp_diamond_comp_eq_qc_comp_verschiebung_of_ordinaryIdempotent_of_bridge.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_CartierDuality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.JZeroNeronObjectAtP

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.JHNeronObjectAtP.exists_units_forall_qc_comp_baseChange_U_comp_diamond_comp_eq_qc_comp_verschiebung_of_ordinaryIdempotent_of_bridge
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H) (hΔ : Function.Injective Δ)
    (hfin : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh) (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hS0 : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hS1 : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hS2 : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
          IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
            (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hS3 : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hS4 : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
            Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    (hS5 : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
          (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
          (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
            (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hS6 : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)

    (hS8 : ∀ (v : ℕ)
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

    (S : Set ℕ) (u : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hu : ∀ v : ℕ, (𝒢.transition v).comp (u (v + 1)) = (u v).comp (𝒢.transition v))
    (huι : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (u v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
      ι v ≫ (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1)

    [NeZero (M / p)]
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (_ : (Dw : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt Pl ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C),
      ∃ h : (inv (𝔛.efib Pl hPl ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥Pl).comp ρ)).base
            ((𝔛.efib Pl hPl ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)

    (Φ : Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) ≃ Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hΦ : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥Pl) (ΓN p M H hpM) p v)
    (hFdiv : ∀ (D D' : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl))),
      (D' : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.mapDomain Φ (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      F (Pic0.mk D) = Pic0.mk D')

    (hpull1sp : ∀ (D : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (x₁ : ↥(GluingData.admissible O.ssFinset)),
      (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) s.1 = 0 ∧
        (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) (Φ s.1) = 0) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb)) • (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0 →
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = GluedPic0.mk O.ssFinset x₁)

    (ε w : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hεε : ∀ v : ℕ, (ε v).comp (ε v) = ε v)
    (hεtr : ∀ v : ℕ, (𝒢.transition v).comp (ε (v + 1)) = (ε v).comp (𝒢.transition v))
    (hεu : ∀ v : ℕ, (ε v).comp (u v) = (u v).comp (ε v))
    (hwtr : ∀ v : ℕ, (𝒢.transition v).comp (w (v + 1)) = (w v).comp (𝒢.transition v))
    (hεw : ∀ v : ℕ, (ε v).comp (w v) = w v) (hwε : ∀ v : ℕ, (w v).comp (ε v) = w v)
    (hwuε : ∀ v : ℕ, (w v).comp ((u v).comp (ε v)) = ε v)
    (huεw : ∀ v : ℕ, ((u v).comp (ε v)).comp (w v) = ε v)

    {𝒢' : PDivisibleGroup Rh p h} (Dual : 𝒢.CartierDuality 𝒢')

    (hc he : ℕ)
    (Gc : ℕ → Type) [∀ v, CommRing (Gc v)] [∀ v, HopfAlgebra (ZMod p) (Gc v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Gc v)] [∀ v, Module.Finite (ZMod p) (Gc v)]
    (Ge : ℕ → Type) [∀ v, CommRing (Ge v)] [∀ v, HopfAlgebra (ZMod p) (Ge v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Ge v)] [∀ v, Module.Finite (ZMod p) (Ge v)]
    (sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v) (se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v)
    (qc : ∀ v, (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] Gc v) (πe : ∀ v, (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] Ge v)
    (σ : ∀ v, Ge v →ₐc[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))
    (Θ : ∀ v, (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] Gc v ⊗[ZMod p] Ge v)
    (hsum : hc + he = h)
    (hGc : ∀ v, IsLocalRing (Gc v)) (hGe : ∀ v, IsReduced (Ge v))
    (hGe' : ∀ v, Algebra.FormallyUnramified (ZMod p) (Ge v))
    (hsc : ∀ v, Function.Surjective (sc v))
    (hrankGc : ∀ v, Module.finrank (ZMod p) (Gc v) = p ^ (v * hc))
    (hkerGc : ∀ v, RingHom.ker (sc v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Gc (v + 1)) (p ^ v))
    (hse : ∀ v, Function.Surjective (se v))
    (hrankGe : ∀ v, Module.finrank (ZMod p) (Ge v) = p ^ (v * he))
    (hkerGe : ∀ v, RingHom.ker (se v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Ge (v + 1)) (p ^ v))
    (hqc : ∀ v, Function.Surjective (qc v)) (hπe : ∀ v, Function.Surjective (πe v))
    (hkerπe : ∀ v, RingHom.ker (πe v : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Ge v) = nilradical (ZMod p ⊗[Rh] 𝒢.level v))
    (hπeσ : ∀ v, (πe v).comp (σ v) = BialgHom.id (ZMod p) (Ge v))
    (hkerqc : ∀ v, RingHom.ker (qc v : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Gc v) =
      Ideal.map (σ v : Ge v →ₐ[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (Ge v))))
    (hΘ : ∀ v, Function.Bijective (Θ v))
    (hΘ' : ∀ v b, Θ v b = Algebra.TensorProduct.map (qc v : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Gc v)
      (πe v : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Ge v) (Coalgebra.comul (R := ZMod p) b))
    (hqcs : ∀ v, (qc v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (sc v).comp (qc (v + 1)))
    (hπes : ∀ v, (πe v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (se v).comp (πe (v + 1)))
    (hsσ : ∀ v, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)).comp (σ (v + 1)) = (σ v).comp (se v))
    (hΘs : ∀ v, (Θ v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (Bialgebra.TensorProduct.map (sc v) (se v)).comp (Θ (v + 1)))

    (VB : ∀ v, (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))
    (hVB1 : ∀ v (b : (ZMod p ⊗[Rh] 𝒢.level v)), (VB v b) ^ p = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p b)
    (hVB2 : ∀ v (b : (ZMod p ⊗[Rh] 𝒢.level v)), VB v (b ^ p) = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p b)
    (hVB3 : ∀ v (φ : CartierDual (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v)) (b : (ZMod p ⊗[Rh] 𝒢.level v)), φ (VB v b) = (φ ^ p) b) :
    ∃ d₀ : (ZMod M)ˣ, ∀ (δ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v),
      (∀ v : ℕ, (𝒢.transition v).comp (δ (v + 1)) = (δ v).comp (𝒢.transition v)) →
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (δ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
        ι v ≫ (O.hecke S (CohCarrier.Gen.dia d₀)).1) →
      (∀ v : ℕ, (ε v).comp (δ v) = (δ v).comp (ε v)) →
      (∀ v : ℕ, (u v).comp (δ v) = (δ v).comp (u v)) →

      ∀ v : ℕ, (qc v : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc v).comp
        (((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ((u v).comp (δ v))).comp
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) :
            ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) :
          ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) =
      (qc v : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc v).comp
        (((VB v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) :
            ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) :
          ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) := by sorry
