-- Prove2me | Theorems.Thm_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins
-- name    : ModularCurve.exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/d0d1db13-5eec-5a7a-b82b-57604c17d5a1
-- title:
--   Component projectors on the mod-p Raynaud quotient
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ and $p^{2} \nmid M$, $H \le (\mathbb{Z}/M)^{\times}$ is a subgroup, and `hHp` requires every unit of $\mathbb{Z}/M$ whose image in $(\mathbb{Z}/(M/p))^{\times}$ is trivial to lie in $H$. Further, $Pl$ is a valuation subring of $\overline{\mathbb{Q}}$ with `hPl : Pl.LiesOverPrime p`, i.e. $p$ lies in the nonunits of $Pl$, its residue field being of characteristic $p$ and algebraically closed; `hj` places the Laurent $q$-expansion `jqModC ℚ` of $j$ in the level-one function field `qExpFunctionFieldC ℚ ⊤`. The base ring is `R p`, the subring $\mathbb{Z}_{(p)} \subset \mathbb{Q}$ of rationals with denominator prime to $p$.
--
--   Geometric and group-theoretic data: $\mathfrak{X}$ is a Deligne–Rapoport model datum `XHDRModelAtP p M H hpM hj` (integral models over `R p` of the curves of level `ΓM M H` and `ΓN p M H hpM`, the degeneracy maps $\mathfrak{X}.\pi$, $\mathfrak{X}.\pi w$ and the involution $\mathfrak{X}.w$, the cusp section $\mathfrak{X}.\varepsilon_{\inf}$, a curve model $\mathfrak{X}.\mathrm{Meta}$ of $\overline{\mathbb{Q}}$ together with the fibre models $\mathfrak{X}.\mathrm{Mfib}$, the diamond automorphisms $\mathfrak{X}.\mathrm{dia0}$, and the Galois pin); $\Lambda$ is a `JHNeronObjectAtP.LevelData` for the level $M/p$ (a point $\Lambda.\sigma_A$ of `base p` supported at $Pl$, a scheme $\Lambda.X$ with structure morphism $\Lambda.f$, a relative group law $\Lambda.L$, and bijections $\Lambda.\mathrm{pts}$, $\Lambda.\mathrm{ptsSp}$ between $J_H(M/p,\;\mathrm{infSubgroup}\,H)$, resp. $\mathrm{Pic}^{0}$ of the level-`ΓN` function field over the residue field of $Pl$, and sections over the generic, resp. residue, point); and $O$ is a `JHNeronObjectAtP` for these data at level $M$. The hypotheses `hrep` and `hrepΛ` assert that the designations $(O.G, O.g)$ and $(\Lambda.X, \Lambda.f)$, each with zero section the unit of its group law, represent the subfunctor of the relative Picard functor cut out by `algEquivZeroCut` (fibrewise algebraically trivial rigidified line bundles) for the `ΓM`-curve rigidified along $\mathfrak{X}.\varepsilon_{\inf}$, respectively for the `ΓN`-curve rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$.
--
--   The henselian base: $R_h$ is a henselian local domain and a discrete valuation ring, faithfully an $\overline{\mathbb{Q}}$-algebra, with `hRA` putting the image of $R_h$ inside $Pl$, `hRloc` identifying the maximal ideal of $R_h$ with the elements of valuation $<1$, and `hres` identifying the kernel of a given map $R_h \to \mathbb{Z}/p$ with the same set.
--
--   Hecke bookkeeping and pins: $S \subseteq \mathbb{N}$ and $d \in (\mathbb{Z}/M)^{\times}$ with `hd` saying that the image of $d$ in $\mathbb{Z}/(M/p)$ is $p$; $\rho :$ `R p` $\to Pl$ with `hρ` compatible with the structural map to $\overline{\mathbb{Q}}$ and `hσA : Λ.σA = Spec.map ρ`. The point-reduction pins `hsp`, `hspΛ` and `hdia0` (many clauses each, summarised here) say: for $i \in \{0,1\}$, given two $\overline{\mathbb{Q}}$-points $y_1,y_2$ of $\mathfrak{X}.\mathrm{Meta}.C$, integral lifts $u_1,u_2$ over $Pl$ meeting the smooth locus, their reductions $u\kappa_1,u\kappa_2$, closed points of the fibre model lying over those reductions, the degree-zero divisor $(y_1)-(y_2)$ and an admissible glued datum whose two divisor components are $(P_1)-(P_2)$ in the slot indexed by $i$ and $0$ in the other, with vanishing unit component, the corresponding section of $O.g$ (resp. of $\Lambda.f$ after applying $O.\mathrm{degPts}\,i$) exists over $\Lambda.\sigma_A$ and reduces to the prescribed class in `GluedPic0` (resp. in $\mathrm{Pic}^0$ of the special fibre); and the diamond automorphisms $\mathfrak{X}.\mathrm{dia0}\,e$ carry closed points of the fibre model to closed points whose place is the `diamondActionModL` translate.
--
--   Special-fibre operators: additive endomorphisms $F, F^{\mathrm{inv}}, F^{*}$ of $\mathrm{Pic}^{0}$ of the level-`ΓN` function field over the residue field, with `hF` identifying $F$ with `qExpFrobeniusPushforwardModL`, `hFinv` making $F$ and $F^{\mathrm{inv}}$ mutually inverse, and `hFstar` giving $F^{*} = p\,F^{\mathrm{inv}}$; a unit $pb$ of $(\mathbb{Z}/(M/p))^{\times}$ reducing to $p$ (`hpb`) and the diamond operator $\delta$ it induces (`hδ`); the permutation $\Phi$ of places with `hΦ` identifying it with `qExpFrobeniusPlaceModL` and `hFdiv` tying $F$ on divisor classes to $\Phi$-pushforward of divisors.
--
--   Degeneracy and Atkin–Lehner data: $\alpha^{\mathrm{pull}} : \mathrm{Fin}\,2 \to (J_H(M/p) \to J_H(M,H))$, morphisms $\mathrm{degPull}\,i : \Lambda.X \to O.G$ over the base, with `hpull` their effect on generic points, `hpull_mul` their multiplicativity for the two group laws, `hpullsp` computing, through `GluedPic0.toPic0Pair`, the reduction of $\mathrm{degPull}\,i$ as $(x, F^{*}x)$ for $i=0$ and $(F^{*}x, \delta x)$ for $i=1$, and `hpull1sp` the corresponding divisorial formula for $\mathrm{degPull}\,1$ under support conditions along $O.\mathrm{ssFinset}$ and $\Phi$; an endomorphism $\bar W$ of $J_H(M,H)$ induced by a semilinear automorphism $w^{\mathrm{gen}}$ (`hWbar`) pinned by $\mathfrak{X}.w$ on geometric points (`hwgen`); the generic identity `hUPgen` asserting $U_p x + \bar W x = \alpha^{\mathrm{pull}}_1(O.\mathrm{degPts}_0 x)$ for all $x$; and the node shift: a permutation $\sigma$ of $O.\mathrm{ssFinset}$ with `hσ` $(\sigma n)_2 = n_1$. The morphism $\Lambda.f$ is separated and locally of finite type.
--
--   The finite part: $\mathcal{G}$ is a $p$-divisible group over $R_h$ of height $h$, $\Delta$ an additive map from its $\overline{\mathbb{Q}}$-points to $J_H(M,H)$ and $e$ a $\mathbb{Z}_p$-linear map of Tate modules, subject to `hΔinj` (injectivity), `hΔlev` (the image of the level-$v$ points is exactly $O.\mathrm{finPts}(p^{v})$, the subgroup generated by the $p^{v}$-torsion classes whose point extends to the place), `hΔgal` (Galois equivariance), `hΔhecke` (every Hecke generator is realised by a transition-compatible family of bialgebra endomorphisms of the levels of $\mathcal{G}$ compatible with $\Delta$ and `genOpH`), `he` (componentwise description of $e$ through $\Delta$), `heinj`, `herange` (the image of $e$ consists of the sequences whose $n$-th term lies in $O.\mathrm{finPts}(p^{n})$), `hegal`, `hsat` (saturation of the image), `hcoker` (the cokernel of $e$ is free of rank $O.\mathrm{toricRank}$) and `htor` (toric points of level $p^{v}$ lie in the image).
--
--   The Raynaud quotient: $\mathcal{B}$ is a $p$-divisible group over $R_h$ of height $h_B$ with a family $\psi_v : \mathcal{B}.\mathrm{level}\,v \to \mathcal{G}.\mathrm{level}\,v$ of bialgebra maps; `hhB` gives $h = O.\mathrm{toricRank} + h_B$ and `hhB2` gives $h_B = 2h'$; `hψt` is transition compatibility, `hψker` says a level-$v$ point of $\mathcal{G}$ restricts to the identity on $\mathcal{B}$ exactly when its image under $\Delta$ lies in $O.\mathrm{toricPts}(p^{v})$, `hψsurj` is surjectivity on points, `hψred` a reduction criterion transferring integrality from $\mathcal{B}$ to $\mathcal{G}$, and `hperiod` the inertia-period condition: for $\sigma$ in the inertia subgroup of $Pl$ over $\mathbb{Q}$ and $z$ a $p^{v}$-torsion class, a point $y$ with $\Delta y = \sigma z - z$ becomes infinitesimal on $\mathcal{B}$.
--
--   The geometric pins over $R_h$: $\rho_h :$ `R p` $\to R_h$ with `hρh`, and immersions $\iota_v : \mathrm{Spec}(\mathcal{G}.\mathrm{level}\,v) \to O.G$ with `hιbase` (the structure morphism), `hιcl` (the induced map to the fibre product is a closed immersion), `hιp` (multiplication by $p^{v}$ on $\iota_v$ is the unit section), `hιpts` (compatibility with $\Delta$ on points), `hιmul` (additivity for the relative group law), `hιt` (compatibility with transitions), `hιhecke` (each Hecke generator is realised both on the levels of $\mathcal{G}$ and by $O.\mathrm{hecke}$, compatibly with $\Delta$), and `hιfin` (the induced map into the $p^{v}$-torsion fibre product is an open and closed immersion meeting every point above the closed point of $R_h$). The operators $u_v$ (bialgebra endomorphisms, transition compatible by `hut`, realising $O.\mathrm{hecke}\,S\,U_p$ by `huι`) and $D_{p,v}$ (bialgebra automorphisms, transition compatible by `hDpt`, realising $O.\mathrm{hecke}\,S\,\langle d\rangle$ by `hDpι`) preserve the toric points (`hutor`, `hDptor`), and they descend along $\psi$ to families $u_{B,v}$ and $D_{B,v}$ on $\mathcal{B}$ (`huB`, `hDB`), with $D'_{B,v}$ the base change of $D_{B,v}$ to $\mathbb{Z}/p$ (`hDB'`).
--
--   The mod-$p$ data: $\sigma_p : \mathrm{Spec}(\mathbb{Z}/p) \to$ `base p` with `hσp`; morphisms $\iota^{p}_{v} : \mathrm{Spec}(\mathbb{Z}/p \otimes_{R_h} \mathcal{G}.\mathrm{level}\,v) \to O.G \times_{\text{base}} \mathrm{Spec}(\mathbb{Z}/p)$ with `hιp₁`, `hιp₂` describing their two projections; and morphisms $q_i$, $i \in \{0,1\}$, from the base change of $O.g$ along $\sigma_p$ to the base change of $\Lambda.f$, which are homomorphic for the base-changed group laws (`hqmul`) and restrict to $O.\mathrm{abqFibre}\,i$ over the residue field of $Pl$ (`hqbc`), the compatibility of the two base points being `hfac`.
--
--   Under all of these, there exist a family $r : \mathrm{Fin}\,2 \to \forall v, \mathrm{Spec}\bigl((\mathcal{B} \otimes \mathbb{Z}/p).\mathrm{level}\,v\bigr) \to \Lambda.X \times_{\text{base}} \mathrm{Spec}(\mathbb{Z}/p)$ and two families $\varepsilon_v, \varepsilon'_v$ of $\mathbb{Z}/p$-bialgebra endomorphisms of $(\mathcal{B} \otimes \mathbb{Z}/p).\mathrm{level}\,v$ such that:
--
--   for all $i$ and $v$, $\mathrm{Spec}$ of $\mathrm{id}_{\mathbb{Z}/p} \otimes \psi_v$ followed by $r_{i,v}$ equals $\iota^{p}_{v}$ followed by $q_i$ (so the composites factor through the Raynaud quotient); for all $v$, $\mathrm{Spec}(\varepsilon_v)$ followed by $r_{1,v}$ is the structural map $\mathrm{Spec}$ of $\mathbb{Z}/p \to (\mathcal{B}\otimes\mathbb{Z}/p).\mathrm{level}\,v$ followed by the unit section of the base-changed group law $\Lambda.L$, while $\mathrm{Spec}(\varepsilon_v)$ followed by $r_{0,v}$ is $r_{0,v}$; symmetrically, $\mathrm{Spec}(\varepsilon'_v)$ followed by $r_{0,v}$ is that same unit section and $\mathrm{Spec}(\varepsilon'_v)$ followed by $r_{1,v}$ is $r_{1,v}$; each $\varepsilon_v$ and each $\varepsilon'_v$ is idempotent for composition; both composites $\varepsilon_v \circ \varepsilon'_v$ and $\varepsilon'_v \circ \varepsilon_v$ equal, as $\mathbb{Z}/p$-algebra maps, the unit map composed with the counit; the convolution product of $\varepsilon_v$ and $\varepsilon'_v$ in `WithConv` is the identity; both families commute with the transition maps of $\mathcal{B} \otimes \mathbb{Z}/p$, that is $\mathrm{transition}_v \circ \varepsilon_{v+1} = \varepsilon_v \circ \mathrm{transition}_v$ and likewise for $\varepsilon'$; the triangularity identity $\varepsilon_v \circ (\mathrm{id} \otimes u_{B,v}) \circ \varepsilon_v = \varepsilon_v \circ (\mathrm{id} \otimes u_{B,v})$ holds for every $v$; and $\varepsilon_v$ commutes with $D'_{B,v}$ for every $v$.
--
--   This is the splitting of the mod-$p$ Raynaud quotient of the finite part of $J_H$ into two pieces, cut out by a complementary pair of idempotent bialgebra endomorphisms that are pinned geometrically by the two degeneracy maps to level $M/p$, and on which $U_p$ acts triangularly and the diamond operator diagonally — the group-scheme shadow of the Deligne–Rapoport description of the special fibre at a prime exactly dividing the level. It feeds the two-step tower descent for the finite part, [`ModularCurve.exists_twoStepTower_raynaudQuotient_descent_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins`](thm.html#ModularCurve.exists_twoStepTower_raynaudQuotient_descent_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins), in the level-lowering half of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins.lean

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
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
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

theorem ModularCurve.exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins
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
    [IsDiscreteValuationRing Rh]

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
    (Dp : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] 𝒢.level v)
    (hDpt : ∀ v : ℕ, (𝒢.transition v).comp (Dp (v + 1) : 𝒢.level (v + 1) →ₐc[Rh] 𝒢.level (v + 1)) =
      (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (𝒢.transition v))
    (hDpι : ∀ v : ℕ, Spec.map (CommRingCat.ofHom ((Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
      ι v ≫ (O.hecke S (CohCarrier.Gen.dia d)).1)

    (hutor : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v) →
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom x).comp (u v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) ∈ O.toricPts (p ^ v))
    (hDptor : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v) →
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom x).comp ((Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) ∈ O.toricPts (p ^ v))

    (uB : ∀ v : ℕ, ℬ.level v →ₐc[Rh] ℬ.level v) (DB : ∀ v : ℕ, ℬ.level v ≃ₐc[Rh] ℬ.level v)
    (DB' : ∀ v : ℕ, ZMod p ⊗[Rh] ℬ.level v ≃ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v)
    (huB : ∀ v : ℕ, (u v).comp (ψ v) = (ψ v).comp (uB v))
    (hDB : ∀ v : ℕ, (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (ψ v) = (ψ v).comp (DB v : ℬ.level v →ₐc[Rh] ℬ.level v))
    (hDB' : ∀ v : ℕ, (DB' v : ZMod p ⊗[Rh] ℬ.level v →ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v) =
      Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (DB v : ℬ.level v →ₐc[Rh] ℬ.level v))

    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ ModularCurve.JZeroNeronObjectAtP.base p)
    (hσp : Spec.map (CommRingCat.ofHom (algebraMap Rh (ZMod p))) ≫ Spec.map (CommRingCat.ofHom ρh) = σp)
    (ιp : ∀ v : ℕ, Spec (CommRingCat.of (ZMod p ⊗[Rh] 𝒢.level v)) ⟶ pullback O.g σp)
    (hιp₁ : ∀ v : ℕ, ιp v ≫ pullback.fst O.g σp =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : 𝒢.level v →+* ZMod p ⊗[Rh] 𝒢.level v)) ≫ ι v)
    (hιp₂ : ∀ v : ℕ, ιp v ≫ pullback.snd O.g σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))))
    (q : Fin 2 → NeronModelInfra.SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp Λ.f))

    [Algebra (ZMod p) (ResidueField ↥Pl)]
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl))) ≫ σp = ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA)
    (hqmul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : NeronModelInfra.SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange σp).mul s x y) (q i) =
          (Λ.L.baseChange σp).mul s (NeronModelInfra.schemeHomOverComp x (q i)) (NeronModelInfra.schemeHomOverComp y (q i)))
    (hqbc : ∀ i : Fin 2,
        (O.abqFibre i).1 ≫ pullback.map Λ.f (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) Λ.f σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
          pullback.map O.g (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) O.g σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) ≫ (q i).1)
    :
    ∃ (r : Fin 2 → ∀ v : ℕ, Spec (CommRingCat.of ((ℬ.baseChange (ZMod p)).level v)) ⟶ pullback Λ.f σp)
      (ε ε' : ∀ v : ℕ, (ℬ.baseChange (ZMod p)).level v →ₐc[ZMod p] (ℬ.baseChange (ZMod p)).level v),

      (∀ (i : Fin 2) (v : ℕ), Spec.map (CommRingCat.ofHom
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v) : ZMod p ⊗[Rh] ℬ.level v →+* ZMod p ⊗[Rh] 𝒢.level v)) ≫ r i v = ιp v ≫ (q i).1) ∧

      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((ε v) : (ℬ.baseChange (ZMod p)).level v →+* (ℬ.baseChange (ZMod p)).level v)) ≫ r 1 v =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((ℬ.baseChange (ZMod p)).level v))) ≫ ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((ε v) : (ℬ.baseChange (ZMod p)).level v →+* (ℬ.baseChange (ZMod p)).level v)) ≫ r 0 v = r 0 v) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((ε' v) : (ℬ.baseChange (ZMod p)).level v →+* (ℬ.baseChange (ZMod p)).level v)) ≫ r 0 v =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((ℬ.baseChange (ZMod p)).level v))) ≫ ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((ε' v) : (ℬ.baseChange (ZMod p)).level v →+* (ℬ.baseChange (ZMod p)).level v)) ≫ r 1 v = r 1 v) ∧

      (∀ v, (ε v).comp (ε v) = ε v) ∧ (∀ v, (ε' v).comp (ε' v) = ε' v) ∧
      (∀ v, (ε v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v).comp (ε' v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v) =
        (Algebra.ofId (ZMod p) ((ℬ.baseChange (ZMod p)).level v)).comp (Bialgebra.counitAlgHom (ZMod p) ((ℬ.baseChange (ZMod p)).level v))) ∧
      (∀ v, (ε' v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v).comp (ε v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v) =
        (Algebra.ofId (ZMod p) ((ℬ.baseChange (ZMod p)).level v)).comp (Bialgebra.counitAlgHom (ZMod p) ((ℬ.baseChange (ZMod p)).level v))) ∧
      (∀ v, WithConv.toConv (ε v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v) *
          WithConv.toConv (ε' v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v) =
        WithConv.toConv (AlgHom.id (ZMod p) ((ℬ.baseChange (ZMod p)).level v))) ∧
      (∀ v, ((ℬ.baseChange (ZMod p)).transition v).comp (ε (v + 1)) = (ε v).comp ((ℬ.baseChange (ZMod p)).transition v)) ∧
      (∀ v, ((ℬ.baseChange (ZMod p)).transition v).comp (ε' (v + 1)) = (ε' v).comp ((ℬ.baseChange (ZMod p)).transition v)) ∧

      (∀ v, (ε v).comp ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (uB v)).comp (ε v)) =
        (ε v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (uB v))) ∧
      (∀ v, (ε v).comp (DB' v : ZMod p ⊗[Rh] ℬ.level v →ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v) =
        (DB' v : ZMod p ⊗[Rh] ℬ.level v →ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v).comp (ε v)) := by sorry
