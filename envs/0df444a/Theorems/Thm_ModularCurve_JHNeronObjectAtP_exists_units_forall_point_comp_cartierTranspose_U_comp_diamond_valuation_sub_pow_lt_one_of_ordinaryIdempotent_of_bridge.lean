-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_units_forall_point_comp_cartierTranspose_U_comp_diamond_valuation_sub_pow_lt_one_of_ordinaryIdempotent_of_bridge
-- name    : ModularCurve.JHNeronObjectAtP.exists_units_forall_point_comp_cartierTranspose_U_comp_diamond_valuation_sub_pow_lt_one_of_ordinaryIdempotent_of_bridge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/fd5c9ad0-6e0a-54c8-87b1-75a5a37682ef
-- title:
--   Cartier transpose of Uₚ⟨ d₀⟩ is Frobenius (ordinary part)
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ such that every unit mapping to $1$ under `ZMod.unitsMap` for $M/p \mid M$ lies in $H$ (`hHp`), and a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$ (`hPl`), whose residue field is algebraically closed of characteristic $p$. Fix the hypothesis `hj` that the $q$-expansion [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15) of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤`, a model datum $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over the localisation `R p` of $\mathbb{Z}$ at $p$, a level datum $\Lambda$ of type `JHNeronObjectAtP.LevelData p M H hpM Pl` (a section $\sigma_A$ of the base over $Pl$, a scheme $\Lambda.X$ with relative group law $\Lambda.L$, and identifications of $J_H(M/p)$ with its generic points and of $\mathrm{Pic}^0$ of the reduced function field with its points over the residue field), and $O :$ `JHNeronObjectAtP p M H hpM Pl hPl Λ`, the Néron object at level $\Gamma_H(M)$ with group law $O.L$, identification `O.pts` of $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \overline{F}_H(M))$ with the generic points of $O.g$, Hecke endomorphisms `O.hecke S t` indexed by the generators [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13), and `ptsSp` identifying glued $\mathrm{Pic}^0$ classes with points over the residue field. The hypothesis `hrep` asserts that $(O.G, O.g)$ with zero section the unit of $O.L$ represents, as a `RelativePic0Designation`, the subfunctor of rigidified line bundles on $\mathfrak{X}$ (rigidified along $\mathfrak{X}.\varepsilon_{\inf}$) that are fibrewise algebraically equivalent to zero.
--
--   Next, $R_h$ is a henselian local domain, faithfully and algebraically embedded in $\overline{\mathbb{Q}}$, with the hypotheses `hRA` that the image of $R_h$ lies in $Pl$ and `hRloc` that $x$ lies in the maximal ideal of $R_h$ exactly when its image has $Pl$-valuation $< 1$; an $R_h$-algebra structure on $\mathbb{Z}/p$ is given, with `hres` asserting that $x$ has zero image in $\mathbb{Z}/p$ exactly when its image in $\overline{\mathbb{Q}}$ has $Pl$-valuation $< 1$.
--
--   Let $\mathcal{G}$ be a $p$-divisible group over $R_h$ of height $h$, with levels $\mathcal{G}.\mathrm{level}\,v$ and surjective transition bialgebra maps. The hypotheses pinning $\mathcal{G}$ as the finite part of $O[p^\infty]$ are: an injective additive map $\Delta$ from the points $\mathcal{G}(\overline{\mathbb{Q}})$ to $J_H(M)$; `hfin`, that for each $v$ the subgroup `O.finPts (p ^ v)` is exactly the image under $\Delta$ of the level-$v$ points; a ring map $\rho_h :$ `R p` $\to R_h$ and morphisms $\iota_v : \mathrm{Spec}(\mathcal{G}.\mathrm{level}\,v) \to O.G$ subject to the clauses `hS0`–`hS6` and `hS8` (summarised here): `hS0` compatibility of $\rho_h$ with the structural maps to $\overline{\mathbb{Q}}$; `hS1` that $\iota_v$ followed by $O.g$ is the map induced by $R_h \to \mathcal{G}.\mathrm{level}\,v$ followed by that induced by $\rho_h$; `hS2` that the induced map to the fibre product is a closed immersion; `hS3` that $\iota_v$ followed by multiplication by $p^v$ for $O.L$ factors through the unit section; `hS4` that the $O$-point attached by $\Delta$ to a level-$v$ point $x$ is the map induced by $x$ followed by $\iota_v$; `hS5` that $\iota_v$ transports the group structure on level-$v$ points over any $R_h$-algebra $B$ to the group law $O.L$; `hS6` compatibility of the $\iota_v$ with the transition maps; and `hS8` that the comparison morphism $j_v$ from the $p^v$-kernel of $O.L$ into the relevant fibre product is an open and a closed immersion whose image contains every point lying over the closed point of $R_h$.
--
--   Further data: a set $S$ of naturals and a family $u = (u_v)$ of $R_h$-bialgebra endomorphisms of the levels, compatible with the transitions (`hu`) and realising along $\iota$ the Hecke endomorphism `O.hecke S (CohCarrier.Gen.U p _ hpM)`, i.e. $U_p$ (`huι`); a ring map $\rho :$ `R p` $\to Pl$ with `hρ` stating that $\rho$ followed by the inclusion of $Pl$ is the structural map to $\overline{\mathbb{Q}}$, and `hσA` stating $\Lambda.\sigma_A = \mathrm{Spec}(\rho)$.
--
--   The special-fibre comparison hypotheses are as follows. `hsp`: for each $i \in \{0,1\}$, given $\overline{\mathbb{Q}}$-points $y_1, y_2$ of $\mathfrak{X}.\mathrm{Meta}.C$, lifts $u_1, u_2$ over $\mathrm{Spec}(\rho)$ with image in the smooth locus and agreeing with $y_1, y_2$ over the generic point, residue-field sections $u\kappa_1, u\kappa_2$ of the fibre compatible with $u_1, u_2$, closed points $P_1, P_2$ of the fibre model $\mathfrak{X}.\mathrm{Mfib}$ whose images under the $i$-th component map are the images of the closed point under $u\kappa_1, u\kappa_2$, a degree-zero divisor $Dv = (y_1) - (y_2)$ on the geometric curve, and an admissible gluing datum $x$ whose first component is $(P_1) - (P_2)$ and second component $0$ when $i = 0$, the reverse when $i = 1$, and whose third component vanishes, there exists a section $s$ over $\Lambda.\sigma_A$ with $O.\mathrm{pts}(\mathrm{Pic}^0\text{-class of } Dv)$ equal to the base change of $s$ to $\overline{\mathbb{Q}}$, and whose reduction corresponds under `O.ptsSp` to the glued class of $x$. `hspΛ`: the analogous statement one level down, producing for the degeneracy image `O.degPts i` of the class of $Dv$ a section $s_0$ over $\Lambda.\sigma_A$ for $\Lambda.f$ whose reduction is the class of a prescribed degree-zero divisor $Dw = (Q_1) - (Q_2)$ on the reduced function field, where $Q_1, Q_2$ are closed points of the fibre model matching $u\kappa_1, u\kappa_2$ along $\mathfrak{X}.\pi$ or $\mathfrak{X}.\pi_w$ according to $i$. `hdia0`: for each $e \in (\mathbb{Z}/(M/p))^\times$ and closed point $P$ of the fibre model, the point obtained by transporting $P$ along the automorphism $\mathfrak{X}.\mathrm{dia0}\,e$ of the fibre is again closed, and its place is the translate of the place of $P$ by the semilinear automorphism attached to the diamond action `diamondActionModL` of a lift of $e$.
--
--   Frobenius data on the special fibre: additive endomorphisms $F, F^{\mathrm{inv}}, F^{*}$ of $\mathrm{Pic}^0$ of the function field `Fbar p M H hpM` over the residue field of $Pl$, with `hF` identifying $F$ with the Frobenius pushforward `qExpFrobeniusPushforwardModL`, `hFinv` asserting that $F$ and $F^{\mathrm{inv}}$ are mutually inverse, and `hFstar` asserting $F^{*} = p \cdot F^{\mathrm{inv}}$; a unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$ (`hpb`) and the additive endomorphism $\delta$ of $\mathrm{Pic}^0$ given by the diamond action of a lift of $pb$ (`hδ`); a permutation $\Phi$ of the places equal to `qExpFrobeniusPlaceModL` (`hΦ`), together with `hFdiv`: whenever $D'$ is the pushforward of $D$ along $\Phi$, $F$ sends the class of $D$ to the class of $D'$.
--
--   Degeneracy data: maps $\alpha_i : J_H(M/p, \mathrm{infSubgroup}) \to J_H(M)$ and morphisms $\mathrm{degPull}_i$ over the base from $\Lambda.f$ to $O.g$ for $i \in \{0,1\}$, with `hpull` asserting that the $O$-point of $\alpha_i(x)$ is the $\Lambda$-point of $x$ followed by $\mathrm{degPull}_i$, `hpull_mul` that composition with $\mathrm{degPull}_i$ is a homomorphism from $\Lambda.L$ to $O.L$ on points over any base, and `hpullsp` that on reductions the pair of $\mathrm{Pic}^0$-classes attached to the composite is $(z, F^{*}z)$ for $i = 0$ and $(F^{*}z, \delta z)$ for $i = 1$, where $z$ is the class corresponding to the given point. `hpull1sp` refines this: for a degree-zero divisor $D$ vanishing at each gluing place $s$ and at $\Phi(s)$, and an admissible gluing datum $x_1$ whose first component is $p$ times the pushforward of $D$ along $\Phi^{-1}$, whose second component is the $\delta$-translate of $D$, and whose third component vanishes, the reduction of the $\Lambda$-point of the class of $D$ composed with $\mathrm{degPull}_1$ is the glued class of $x_1$. An Atkin–Lehner datum is also given: an additive endomorphism $\overline{W}$ of $J_H(M)$ acting as a semilinear automorphism $w_{\mathrm{gen}}$ (`hWbar`), with `hwgen` relating $w_{\mathrm{gen}}$ to the involution $\mathfrak{X}.w$ on places, and the Eichler relation `hUPgen`: $U_p x + \overline{W}x = \alpha_1(\mathrm{degPts}_0\, x)$ for all $x \in J_H(M)$. Finally, $\sigma$ is a self-equivalence of the gluing index set `O.ssFinset` with $(\sigma n)_2 = n_1$ (`hσ`).
--
--   The ordinary projector is given by two families $\varepsilon = (\varepsilon_v)$ and $w = (w_v)$ of $R_h$-bialgebra endomorphisms of the levels of $\mathcal{G}$ subject to: $\varepsilon_v \circ \varepsilon_v = \varepsilon_v$ (`hεε`); compatibility of $\varepsilon$ and of $w$ with the transitions (`hεtr`, `hwtr`); $\varepsilon_v \circ u_v = u_v \circ \varepsilon_v$ (`hεu`); $\varepsilon_v \circ w_v = w_v$ and $w_v \circ \varepsilon_v = w_v$ (`hεw`, `hwε`); and $w_v \circ (u_v \circ \varepsilon_v) = \varepsilon_v = (u_v \circ \varepsilon_v) \circ w_v$ (`hwuε`, `huεw`), so that $u$ is invertible on the $\varepsilon$-part. Lastly, $\mathcal{G}'$ is a $p$-divisible group over $R_h$ of the same height and $\mathrm{Dual}$ a Cartier duality datum between $\mathcal{G}$ and $\mathcal{G}'$, consisting of bialgebra isomorphisms $\mathrm{Dual}.\mathrm{equiv}_v : \mathcal{G}'.\mathrm{level}\,v \cong \mathrm{CartierDual}_{R_h}(\mathcal{G}.\mathrm{level}\,v)$ compatible with the transitions and multiplication by $p$.
--
--   Under these hypotheses there exists $d_0 \in (\mathbb{Z}/M)^\times$ with the following property. Let $\delta = (\delta_v)$ be any family of $R_h$-bialgebra endomorphisms of the levels of $\mathcal{G}$ such that: the transitions intertwine $\delta_{v+1}$ with $\delta_v$; for every $v$, the morphism induced by $\delta_v$ followed by $\iota_v$ equals $\iota_v$ followed by the Hecke endomorphism `O.hecke S (CohCarrier.Gen.dia d₀)`, the diamond operator $\langle d_0 \rangle$; $\varepsilon_v \circ \delta_v = \delta_v \circ \varepsilon_v$; and $u_v \circ \delta_v = \delta_v \circ u_v$. Then for every level $v$ and every level-$v$ point $\psi$ of $\mathcal{G}'$ with values in $\overline{\mathbb{Q}}$, that is an $R_h$-algebra homomorphism $\psi : \mathcal{G}'.\mathrm{level}\,v \to \overline{\mathbb{Q}}$, such that $\psi(a) \in Pl$ for every $a$, and such that $\psi$ is fixed by the Cartier transpose of $\varepsilon_v$, namely
--   $$\psi \circ \big(\mathrm{Dual}.\mathrm{equiv}_v^{-1} \circ \mathrm{CartierDual.map}(\varepsilon_v) \circ \mathrm{Dual}.\mathrm{equiv}_v\big) = \psi,$$
--   every $a \in \mathcal{G}'.\mathrm{level}\,v$ satisfies
--   $$Pl\text{-}\mathrm{val}\Big(\psi\big(\mathrm{Dual}.\mathrm{equiv}_v^{-1} \circ \mathrm{CartierDual.map}(u_v \circ \delta_v) \circ \mathrm{Dual}.\mathrm{equiv}_v\,(a)\big) - \psi(a)^p\Big) < 1 .$$
--   That is, on the $\varepsilon$-part of the Cartier dual the transpose of $U_p\langle d_0\rangle$ agrees with the $p$-power map modulo the maximal ideal of $Pl$.
--
--   This is the Hecke-theoretic half of the Eichler–Shimura congruence "Frobenius $= U_p\langle d_0\rangle$" at a prime $p$ exactly dividing the level $M$, formulated on the Cartier dual of the ordinary ($\varepsilon$-)part of the finite part of the $p$-divisible group of the Néron object of $J_H(M)$ at $p$. It is used, together with the Galois-theoretic computation of Frobenius on the formal part of a Tate module and the perfectness of the Cartier pairing, to show that an arithmetic Frobenius acts on the multiplicative part of the ordinary factor of $T_p J_H(M)$ through $U_p\langle d_0\rangle$ times the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_units_forall_point_comp_cartierTranspose_U_comp_diamond_valuation_sub_pow_lt_one_of_ordinaryIdempotent_of_bridge.lean

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

theorem ModularCurve.JHNeronObjectAtP.exists_units_forall_point_comp_cartierTranspose_U_comp_diamond_valuation_sub_pow_lt_one_of_ordinaryIdempotent_of_bridge
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

    {𝒢' : PDivisibleGroup Rh p h} (Dual : 𝒢.CartierDuality 𝒢') :
    ∃ d₀ : (ZMod M)ˣ, ∀ (δ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v),
      (∀ v : ℕ, (𝒢.transition v).comp (δ (v + 1)) = (δ v).comp (𝒢.transition v)) →
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (δ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
        ι v ≫ (O.hecke S (CohCarrier.Gen.dia d₀)).1) →
      (∀ v : ℕ, (ε v).comp (δ v) = (δ v).comp (ε v)) →
      (∀ v : ℕ, (u v).comp (δ v) = (δ v).comp (u v)) →
      ∀ (v : ℕ) (ψ : 𝒢'.Point (AlgebraicClosure ℚ) v),

        (∀ a : 𝒢'.level v, PDivisibleGroup.Point.toAlgHom ψ a ∈ Pl) →

        (PDivisibleGroup.Point.toAlgHom ψ).comp (((Dual.equiv v).symm : CartierDual Rh (𝒢.level v) →ₐc[Rh] 𝒢'.level v).comp
            ((CartierDual.map (ε v)).comp (Dual.equiv v : 𝒢'.level v →ₐc[Rh] CartierDual Rh (𝒢.level v))) :
              𝒢'.level v →ₐ[Rh] 𝒢'.level v) = PDivisibleGroup.Point.toAlgHom ψ →

        ∀ a : 𝒢'.level v,
          Pl.valuation ((PDivisibleGroup.Point.toAlgHom ψ).comp (((Dual.equiv v).symm : CartierDual Rh (𝒢.level v) →ₐc[Rh] 𝒢'.level v).comp
            ((CartierDual.map ((u v).comp (δ v))).comp (Dual.equiv v : 𝒢'.level v →ₐc[Rh] CartierDual Rh (𝒢.level v))) :
              𝒢'.level v →ₐ[Rh] 𝒢'.level v) a -
            PDivisibleGroup.Point.toAlgHom ψ a ^ p) < 1 := by sorry
