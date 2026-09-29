-- Prove2me | Theorems.Thm_ModularCurve_exists_twoStepTower_raynaudQuotient_descent_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins
-- name    : ModularCurve.exists_twoStepTower_raynaudQuotient_descent_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/502e477c-66ff-54d5-b303-3757a3d19cf2
-- title:
--   Two-step special-fibre tower of the Raynaud quotient with descended Uₚ
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial (`hHp`). Fix a valuation subring $\mathfrak{P} =$ `Pl` of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $\mathfrak{P}$ (`hPl`), whose residue field is algebraically closed of characteristic $p$, and the hypothesis `hj` that the $q$-expansion of $j$ lies in the function field of level $\mathrm{SL}_2(\mathbb{Z})$. The geometric input consists of a Deligne–Rapoport-type model $\mathfrak{X} =$ `𝔛 : XHDRModelAtP p M H hpM hj` for the two levels $\Gamma_M$ and $\Gamma_N$ over $R_p = \mathbb{Z}_{(p)} \cap \mathbb{Q}$, a lower-level datum $\Lambda$ (a scheme $\Lambda.X$ over `base p` with a relative group law $\Lambda.L$, a dictionary $\Lambda.\mathrm{pts}$ between $J_H(M/p)$ for the pushed-down subgroup `infSubgroup p M H hpM` and the generic points of $\Lambda.f$, and a dictionary $\Lambda.\mathrm{ptsSp}$ between $\mathrm{Pic}^0$ of the special-fibre function field `Fbar p M H hpM (ResidueField ↥Pl)` and the points of $\Lambda.f$ over the residue point), and a Néron object $O$ at level $M$ with group law $O.L$, point dictionaries $O.\mathrm{pts}$, $O.\mathrm{ptsSp}$ and Hecke correspondences $O.\mathrm{hecke}$.
--
--   The representability hypotheses `hrep` and `hrepΛ` assert that $(O.G, O.g)$ together with the unit section of $O.L$ represents the relative $\mathrm{Pic}^0$-subfunctor cut out by the condition `algEquivZeroCut` (fibrewise algebraic equivalence to zero of rigidified line bundles) for the curve `toBase p (ΓM M H) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$, and that $(\Lambda.X, \Lambda.f)$ with the unit section of $\Lambda.L$ does the same for the curve `toBase p (ΓN p M H hpM) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$.
--
--   The base ring hypotheses: $R_h$ is a henselian local discrete valuation domain, faithfully an $R_h$-algebra inside $\overline{\mathbb{Q}}$, with $R_h \subseteq \mathfrak{P}$ (`hRA`), with maximal ideal exactly the elements of valuation $< 1$ (`hRloc`), and carrying an $\mathbb{F}_p$-algebra structure whose kernel is again the set of elements of valuation $< 1$ (`hres`). A set $S \subseteq \mathbb{N}$ and a unit $d \in (\mathbb{Z}/M)^\times$ whose image in $\mathbb{Z}/(M/p)$ is $p$ (`hd`) are fixed, together with a ring map $\rho : R_p \to \mathfrak{P}$ compatible with the structure map to $\overline{\mathbb{Q}}$ (`hρ`) and the identification $\Lambda.\sigma_A = \operatorname{Spec}\rho$ (`hσA`).
--
--   The bridge hypotheses pin the special-fibre dictionaries and operators, and are named here. `hsp`: for each $i \in \{0,1\}$, given geometric points $y_1, y_2$ of $\mathfrak{X}.\mathrm{Meta}$, lifts $u_1, u_2$ of them to $\mathfrak{P}$-points of $X_p(\Gamma_M)$ landing in $\mathfrak{X}.\mathrm{smoothLocus}$, residue-field points $u_{\kappa,1}, u_{\kappa,2}$ of the fibre compatible with the $u_j$ and sectional over the base, closed points $P_1, P_2$ of the special-fibre curve model $\mathfrak{X}.\mathrm{Mfib}$ whose images under $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component map $\mathfrak{X}.\mathrm{comp}\,i$ are the closed points of $u_{\kappa,j}$, a degree-zero divisor $D_v = (y_1) - (y_2)$ on the geometric function field, and an admissible gluing datum $x$ over $O.\mathrm{ssFinset}$ whose first component is $(P_1)-(P_2)$ when $i = 0$ and $0$ otherwise, whose second component is $(P_1)-(P_2)$ when $i = 1$ and $0$ otherwise, and whose unit component vanishes, there is a point $s$ of $O.G$ over $\Lambda.\sigma_A$ with $O.\mathrm{pts}[D_v]$ the restriction of $s$ to $\overline{\mathbb{Q}}$ and with $O.\mathrm{ptsSp}^{-1}$ of the reduction of $s$ equal to the glued class of $x$. `hspΛ` is the analogous statement one level down, with $Q_1, Q_2$ reducing through the fibre map of $\mathfrak{X}.\pi$ (for $i=0$) or $\mathfrak{X}.\pi_w$ (for $i=1$), producing $s_0$ with $\Lambda.\mathrm{pts}(O.\mathrm{degPts}\,i\,[D_v])$ generic and $\Lambda.\mathrm{ptsSp}^{-1}$ of its reduction equal to $[D_w]$, $D_w = (Q_1)-(Q_2)$. `hdia0`: the automorphism $\mathfrak{X}.\mathrm{dia}_0(e)$ moves closed points of the special-fibre model according to the diamond action `diamondActionModL` at the lift [`CuspForm.gammaLift (M/p) e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36), viewed as a semilinear automorphism acting on places. `hF`, `hFinv`, `hFstar`: $F$ is the $q$-expansion Frobenius push-forward on $\mathrm{Pic}^0$ of the special-fibre function field, $F_{\mathrm{inv}}$ is a two-sided inverse of $F$, and $F^\ast = p\,F_{\mathrm{inv}}$. `hpb`, `hδ`: $\delta$ is the diamond operator at a unit $pb \equiv p$. `hpull`, `hpullsp`, `hpull_mul`: the additive maps $\alpha_{\mathrm{pull}}(i) : J_H(M/p) \to J_H(M)$ and the morphisms $\mathrm{degPull}(i) : \Lambda.f \to O.g$ correspond on generic points, their effect on reductions is $(\Lambda.\mathrm{ptsSp}^{-1}x, F^\ast(\cdot))$ for $i=0$ and $(F^\ast(\cdot), \delta(\cdot))$ for $i=1$ after passing to the pair of $\mathrm{Pic}^0$-components of a glued class, and each $\mathrm{degPull}(i)$ is a homomorphism for the group laws. `hWbar`, `hwgen`: $\overline{W}$ is the action of a semilinear automorphism $w_{\mathrm{gen}}$ pinned by the Atkin–Lehner involution $\mathfrak{X}.w$ on places. `hUPgen`: the Eichler–Shimura identity $U_p x + \overline{W}x = \alpha_{\mathrm{pull}}(1)(O.\mathrm{degPts}\,0\,x)$ for all $x \in J_H(M)$. `hσ`: a permutation $\sigma$ of $O.\mathrm{ssFinset}$ with $(\sigma n)_2 = n_1$. `hΦ`, `hFdiv`: $\Phi$ is the Frobenius permutation of places and $F$ is computed by $\Phi$-push-forward of divisors. `hpull1sp`: the reduction of $\mathrm{degPull}(1)$ applied to $\Lambda.\mathrm{ptsSp}[D]$ is the glued class of any admissible datum $x_1$ whose components are $p\,\Phi_\ast^{-1}D$, the diamond translate of $D$ at $pb$, and $0$, provided $D$ vanishes at the nodes and at their Frobenius images. Finally $\Lambda.f$ is separated and locally of finite type.
--
--   The $p$-divisible input: a $p$-divisible group $\mathcal{G}$ over $R_h$ of height $h$, an additive map $\Delta$ from its $\overline{\mathbb{Q}}$-points to $J_H(M)$ and a $\mathbb{Z}_p$-linear map $e$ of Tate modules, subject to `hΔinj` ($\Delta$ injective), `hΔlev` (the image of the level-$v$ points is exactly $O.\mathrm{finPts}(p^v)$), `hΔgal` (Galois equivariance), `hΔhecke` (each Hecke generator is induced along $\Delta$ by a transition-compatible family of $R_h$-bialgebra endomorphisms of the levels), `he` (the components of $e$ are given by $\Delta$), `heinj`, `herange` (the image of $e$ consists of the tuples with $n$-th entry in $O.\mathrm{finPts}(p^n)$), `hegal`, `hsat` (the image of $e$ is saturated for multiplication by $p$), `hcoker` (the cokernel of $e$ is free of rank $O.\mathrm{toricRank}$) and `htor` (the toric points at $p^v$ lie in the image of the level-$v$ points). The Raynaud quotient data: a $p$-divisible group $\mathcal{B}$ over $R_h$ of height $h_B$ with levelwise bialgebra maps $\psi_v : \mathcal{B}.\mathrm{level}\,v \to \mathcal{G}.\mathrm{level}\,v$, a natural number $h'$, and the hypotheses `hhB` ($h = O.\mathrm{toricRank} + h_B$), `hhB2` ($h_B = 2h'$), `hψt` (compatibility with transitions), `hψker` (a level-$v$ point of $\mathcal{G}$ restricts to the trivial point of $\mathcal{B}$ exactly when its $\Delta$-image lies in $O.\mathrm{toricPts}(p^v)$), `hψsurj` (every point of $\mathcal{B}$ is a restriction), `hψred` (if the restriction of a point is congruent to the counit modulo the maximal ideal, so is the point itself) and `hperiod` (for $\sigma$ in the inertia subgroup at $\mathfrak{P}$ and $p^v$-torsion $z$, a point $y$ with $\Delta y = \sigma z - z$ has $\psi$-restriction congruent to the counit). The embedding data: a ring map $\rho_h : R_p \to R_h$ with `hρh`, and morphisms $\iota_v : \operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v) \to O.G$ with `hιbase` (the structure map factorisation), `hιcl` (the induced map to the fibre product is a closed immersion), `hιp` ($\iota_v$ is killed by $[p^v]$), `hιpts` ($\iota_v$ computes $O.\mathrm{pts} \circ \Delta$), `hιmul` (multiplicativity for the group law on arbitrary $R_h$-algebra points), `hιt` (compatibility with transitions), `hιhecke` (each Hecke generator is realised by a transition-compatible family of bialgebra endomorphisms intertwined with $O.\mathrm{hecke}$ along $\iota$ and inducing the operator on $\Delta$-images), and `hιfin` (the comparison map $j_v$ from the $p^v$-torsion into the pullback is both an open and a closed immersion, and its image contains every point over the closed point of $R_h$). Finally, a transition-compatible family $u_v$ of $R_h$-bialgebra endomorphisms of the levels of $\mathcal{G}$ intertwined with $O.\mathrm{hecke}\,S\,U_p$ along $\iota$ (`hut`, `huι`).
--
--   The conclusion asserts the existence of: bialgebra automorphisms $D_p(v)$ of $\mathcal{G}.\mathrm{level}\,v$ over $R_h$; a family $T$ of finite free cocommutative $\mathbb{F}_p$-Hopf algebras with transitions $t^T_v : T(v+1) \to T v$, surjections $\pi^T_v : \mathbb{F}_p \otimes_{R_h} \mathcal{G}.\mathrm{level}\,v \to T v$ and automorphisms $\mathrm{Ver}^T_v$ of $T v$; a height $h_1$ with a family $G_1$ of the same kind, transitions $t_1$ and maps $\pi_1 : \mathbb{F}_p \otimes_{R_h} \mathcal{B}.\mathrm{level}\,v \to G_1 v$; a height $h_2$ with a family $G_2$, transitions $t_2$ and maps $j_2 : G_2 v \to \mathbb{F}_p \otimes_{R_h} \mathcal{B}.\mathrm{level}\,v$; endomorphisms $u^T_v, e^T_v$ of $T v$; endomorphisms $u^B_v$ and automorphisms $D^B_v$ of $\mathcal{B}.\mathrm{level}\,v$ over $R_h$; automorphisms $D^{B\prime}_v$ of $\mathbb{F}_p \otimes_{R_h} \mathcal{B}.\mathrm{level}\,v$; endomorphisms $\varphi_1(v)$ of $G_1 v$, $\varphi_2(v)$ of $G_2 v$, automorphisms $d_2(v)$ of $G_2 v$, and endomorphisms $\mathrm{Ver}_1(v)$ of $G_1 v$, such that all of the following hold.
--
--   (a) $D_p$ commutes with the transitions of $\mathcal{G}$, and $\operatorname{Spec} D_p(v)$ followed by $\iota_v$ equals $\iota_v$ followed by $O.\mathrm{hecke}\,S\,\langle d\rangle$; thus $D_p$ realises the diamond operator at $d$.
--
--   (b) Each $t^T_v$ is surjective, $\dim_{\mathbb{F}_p} T v = p^{v \cdot O.\mathrm{toricRank}}$, $\ker t^T_v$ is the Hopf torsion ideal of $T(v+1)$ at $p^v$, each $\pi^T_v$ is surjective, the $\pi^T$ commute with the transitions ($\pi^T_v \circ (\mathrm{id} \otimes \mathcal{G}.\mathrm{transition}_v) = t^T_v \circ \pi^T_{v+1}$), and for every $\chi$ in the Cartier dual of $T v$ one has $\mathrm{CartierDual.map}(\mathrm{Ver}^T_v)\chi = \chi^p$.
--
--   (c) $\mathrm{id} \otimes \mathcal{B}.\mathrm{transition}_v$ is surjective, $\dim_{\mathbb{F}_p}(\mathbb{F}_p \otimes_{R_h} \mathcal{B}.\mathrm{level}\,v) = p^{v h_B}$, its kernel is the Hopf torsion ideal at $p^v$, $\mathrm{id}\otimes \psi_v$ is injective and compatible with the transitions, and $\ker \pi^T_v$ is the ideal generated by the image under $\mathrm{id}\otimes\psi_v$ of the augmentation ideal (the kernel of the counit) of $\mathbb{F}_p \otimes_{R_h}\mathcal{B}.\mathrm{level}\,v$.
--
--   (d) $h_1 = h_2$ and $h_1 + h_2 = h_B$; each $t_1(v)$ is surjective, $\dim_{\mathbb{F}_p} G_1 v = p^{v h_1}$, $\ker t_1(v)$ is the Hopf torsion ideal at $p^v$, each $\pi_1(v)$ is surjective and compatible with the transitions; each $t_2(v)$ is surjective, $\dim_{\mathbb{F}_p} G_2 v = p^{v h_2}$, $\ker t_2(v)$ is the Hopf torsion ideal at $p^v$, each $j_2(v)$ is injective and compatible with the transitions, and $\ker \pi_1(v)$ is the ideal generated by the image under $j_2(v)$ of the augmentation ideal of $G_2 v$.
--
--   (e) $\pi^T_v \circ (\mathrm{id}\otimes u_v) = u^T_v \circ \pi^T_v$ and $\pi^T_v \circ (\mathrm{id}\otimes D_p(v)) = e^T_v \circ \pi^T_v$.
--
--   (f) $u_v \circ \psi_v = \psi_v \circ u^B_v$ and $D_p(v)\circ\psi_v = \psi_v \circ D^B_v$, and both $u^B$ and $D^B$ commute with the transitions of $\mathcal{B}$.
--
--   (g) $D^{B\prime}_v = \mathrm{id}\otimes D^B_v$, and the reductions of $u$ and of $D_p$ intertwine with $\mathrm{id}\otimes\psi_v$ the reductions of $u^B$ and $D^{B\prime}$ respectively.
--
--   (h) $\pi_1(v)\circ(\mathrm{id}\otimes u^B_v) = \varphi_1(v)\circ \pi_1(v)$, $(\mathrm{id}\otimes u^B_v)\circ j_2(v) = j_2(v)\circ\varphi_2(v)$, and both $\mathrm{id}\otimes D^B_v$ and $D^{B\prime}_v$ intertwine $j_2(v)$ with $d_2(v)$.
--
--   (i) For every $\chi$ in the Cartier dual of $G_1 v$, $\mathrm{CartierDual.map}(\mathrm{Ver}_1(v))\chi = \chi^p$.
--
--   (j) $\varphi_1(v) = \mathrm{Ver}_1(v)$ for all $v$, and $\varphi_2(v)x = d_2(v)(x^p)$ for all $v$ and all $x \in G_2 v$.
--
--   This is the special-fibre analysis of the finite part of $J_H(M)$ at a prime $p$ exactly dividing $M$: the mod-$p$ fibre of the $p$-divisible group $\mathcal{G}$ attached to the finite part is presented as a two-step tower, a multiplicative (toric) quotient $T$ of height the toric rank together with the two halves $G_1$, $G_2$ of the Raynaud quotient $\mathcal{B}$, and the descended operators are identified: $U_p$ acts as Verschiebung on the first half and as $\langle p\rangle$ composed with Frobenius on the second. It is used by [`ModularCurve.JHNeronObjectAtP.exists_pow_cartierDual_reduction_U_eq_frobenius_conv_verschiebung_of_finPtsWitness_of_isDiscreteValuationRing_of_bridge`](thm.html#ModularCurve.JHNeronObjectAtP.exists_pow_cartierDual_reduction_U_eq_frobenius_conv_verschiebung_of_finPtsWitness_of_isDiscreteValuationRing_of_bridge), in the chain establishing the multiplicative behaviour of $U_p$ at $p \parallel M$ that feeds the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_twoStepTower_raynaudQuotient_descent_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
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
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

set_option maxHeartbeats 800000 in

theorem ModularCurve.exists_twoStepTower_raynaudQuotient_descent_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins
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

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh] [IsDiscreteValuationRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    (S : Set ℕ) (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))

    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
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
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (ModularCurve.XHDRLevel.ΓN p M H hpM) p z)
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
    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)

    (Φ : Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) ≃ Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hΦ : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥Pl) (ModularCurve.XHDRLevel.ΓN p M H hpM) p v)
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
    [IsSeparated Λ.f] [LocallyOfFiniteType Λ.f]

    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H))
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (he : ∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e x : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n =
        Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))
    (heinj : Function.Injective e)
    (herange : ∀ y : TateModule p (ModularCurve.JH M H), y ∈ LinearMap.range e ↔
      ∀ n : ℕ, (y : ℕ → ModularCurve.JH M H) n ∈ O.finPts (p ^ n))
    (hegal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
        e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) = ModularCurve.JH.tateGaloisRep M H p τ (e x))
    (hsat : ∀ y : TateModule p (ModularCurve.JH M H), (p : ℤ_[p]) • y ∈ LinearMap.range e → y ∈ LinearMap.range e)
    (hcoker : Nonempty ((TateModule p (ModularCurve.JH M H) ⧸ LinearMap.range e) ≃ₗ[ℤ_[p]] (Fin O.toricRank → ℤ_[p])))
    (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    {hB : ℕ}
    (ℬ : PDivisibleGroup Rh p hB)
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v)
    {h' : ℕ}
    (hhB : h = O.toricRank + hB)
    (hhB2 : hB = 2 * h')
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) = b)
    (hψred : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (hperiod : ∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
      ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
        (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
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

    (u : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hut : ∀ v : ℕ, (𝒢.transition v).comp (u (v + 1)) = (u v).comp (𝒢.transition v))
    (huι : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (u v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1)
    :
    ∃
      (Dp : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] 𝒢.level v)

      (T : ℕ → Type) (_ : ∀ v, CommRing (T v)) (_ : ∀ v, HopfAlgebra (ZMod p) (T v))
        (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (T v)) (_ : ∀ v, Module.Finite (ZMod p) (T v)) (_ : ∀ v, Module.Free (ZMod p) (T v))
      (tT : ∀ v, T (v + 1) →ₐc[ZMod p] T v)
      (πT : ∀ v : ℕ, ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] T v)
      (VerT : ∀ v : ℕ, T v ≃ₐc[ZMod p] T v)

      (h₁ : ℕ) (G₁ : ℕ → Type) (_ : ∀ v, CommRing (G₁ v)) (_ : ∀ v, HopfAlgebra (ZMod p) (G₁ v))
        (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (G₁ v)) (_ : ∀ v, Module.Finite (ZMod p) (G₁ v)) (_ : ∀ v, Module.Free (ZMod p) (G₁ v))
      (t₁ : ∀ v, G₁ (v + 1) →ₐc[ZMod p] G₁ v)
      (π₁ : ∀ v : ℕ, ZMod p ⊗[Rh] ℬ.level v →ₐc[ZMod p] G₁ v)
      (h₂ : ℕ) (G₂ : ℕ → Type) (_ : ∀ v, CommRing (G₂ v)) (_ : ∀ v, HopfAlgebra (ZMod p) (G₂ v))
        (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (G₂ v)) (_ : ∀ v, Module.Finite (ZMod p) (G₂ v)) (_ : ∀ v, Module.Free (ZMod p) (G₂ v))
      (t₂ : ∀ v, G₂ (v + 1) →ₐc[ZMod p] G₂ v)
      (j₂ : ∀ v : ℕ, G₂ v →ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v)

      (uT eT : ∀ v : ℕ, T v →ₐc[ZMod p] T v)
      (uB : ∀ v : ℕ, ℬ.level v →ₐc[Rh] ℬ.level v) (DB : ∀ v : ℕ, ℬ.level v ≃ₐc[Rh] ℬ.level v)
      (DB' : ∀ v : ℕ, ZMod p ⊗[Rh] ℬ.level v ≃ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v)
      (φ₁ : ∀ v : ℕ, G₁ v →ₐc[ZMod p] G₁ v) (φ₂ : ∀ v : ℕ, G₂ v →ₐc[ZMod p] G₂ v) (d₂ : ∀ v : ℕ, G₂ v ≃ₐc[ZMod p] G₂ v)
      (Ver₁ : ∀ v : ℕ, G₁ v →ₐc[ZMod p] G₁ v),

      (∀ v : ℕ, (𝒢.transition v).comp (Dp (v + 1) : 𝒢.level (v + 1) →ₐc[Rh] 𝒢.level (v + 1)) =
        (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
        ι v ≫ (O.hecke S (CohCarrier.Gen.dia d)).1) ∧

      (∀ v, Function.Surjective (tT v)) ∧
      (∀ v, Module.finrank (ZMod p) (T v) = p ^ (v * O.toricRank)) ∧
      (∀ v, RingHom.ker (tT v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (T (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Surjective (πT v)) ∧
      (∀ v : ℕ, (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (tT v).comp (πT (v + 1))) ∧
      (∀ (v : ℕ) (χ : CartierDual (ZMod p) (T v)), CartierDual.map (VerT v : T v →ₐc[ZMod p] T v) χ = χ ^ p) ∧

      (∀ v, Function.Surjective (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ℬ.transition v))) ∧
      (∀ v, Module.finrank (ZMod p) (ZMod p ⊗[Rh] ℬ.level v) = p ^ (v * hB)) ∧
      (∀ v, RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ℬ.transition v)) =
        PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (ZMod p ⊗[Rh] ℬ.level (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v))) ∧
      (∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ (v + 1))) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ℬ.transition v))) ∧
      (∀ v : ℕ, RingHom.ker (πT v : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] T v) =
        Ideal.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v) : ZMod p ⊗[Rh] ℬ.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)
          (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[Rh] ℬ.level v)))) ∧

      h₁ = h₂ ∧ h₁ + h₂ = hB ∧
      (∀ v, Function.Surjective (t₁ v)) ∧
      (∀ v, Module.finrank (ZMod p) (G₁ v) = p ^ (v * h₁)) ∧
      (∀ v, RingHom.ker (t₁ v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G₁ (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Surjective (π₁ v)) ∧
      (∀ v : ℕ, (π₁ v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ℬ.transition v)) = (t₁ v).comp (π₁ (v + 1))) ∧
      (∀ v, Function.Surjective (t₂ v)) ∧
      (∀ v, Module.finrank (ZMod p) (G₂ v) = p ^ (v * h₂)) ∧
      (∀ v, RingHom.ker (t₂ v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G₂ (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Injective (j₂ v)) ∧
      (∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ℬ.transition v)).comp (j₂ (v + 1)) = (j₂ v).comp (t₂ v)) ∧
      (∀ v : ℕ, RingHom.ker (π₁ v : ZMod p ⊗[Rh] ℬ.level v →ₐ[ZMod p] G₁ v) =
        Ideal.map (j₂ v : G₂ v →ₐ[ZMod p] ZMod p ⊗[Rh] ℬ.level v) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (G₂ v)))) ∧

      (∀ v : ℕ, (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) = (uT v).comp (πT v)) ∧
      (∀ v : ℕ, (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v)) = (eT v).comp (πT v)) ∧

      (∀ v : ℕ, (u v).comp (ψ v) = (ψ v).comp (uB v)) ∧
      (∀ v : ℕ, (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (ψ v) = (ψ v).comp (DB v : ℬ.level v →ₐc[Rh] ℬ.level v)) ∧
      (∀ v : ℕ, (ℬ.transition v).comp (uB (v + 1)) = (uB v).comp (ℬ.transition v)) ∧
      (∀ v : ℕ, (ℬ.transition v).comp (DB (v + 1) : ℬ.level (v + 1) →ₐc[Rh] ℬ.level (v + 1)) =
        (DB v : ℬ.level v →ₐc[Rh] ℬ.level v).comp (ℬ.transition v)) ∧

      (∀ v : ℕ, (DB' v : ZMod p ⊗[Rh] ℬ.level v →ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v) = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (DB v : ℬ.level v →ₐc[Rh] ℬ.level v)) ∧
      (∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)) = (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (uB v))) ∧
      (∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v)).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)).comp (DB' v : ZMod p ⊗[Rh] ℬ.level v →ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v)) ∧

      (∀ v : ℕ, (π₁ v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (uB v)) = (φ₁ v).comp (π₁ v)) ∧
      (∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (uB v)).comp (j₂ v) = (j₂ v).comp (φ₂ v)) ∧
      (∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (DB v : ℬ.level v →ₐc[Rh] ℬ.level v)).comp (j₂ v) =
        (j₂ v).comp (d₂ v : G₂ v →ₐc[ZMod p] G₂ v)) ∧
      (∀ v : ℕ, (DB' v : ZMod p ⊗[Rh] ℬ.level v →ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v).comp (j₂ v) = (j₂ v).comp (d₂ v : G₂ v →ₐc[ZMod p] G₂ v)) ∧

      (∀ (v : ℕ) (χ : CartierDual (ZMod p) (G₁ v)), CartierDual.map (Ver₁ v) χ = χ ^ p) ∧

      (∀ v : ℕ, φ₁ v = Ver₁ v) ∧
      (∀ (v : ℕ) (x : G₂ v), φ₂ v x = (d₂ v) (x ^ p)) := by sorry
