-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull
-- name    : ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/aa5b3b87-4321-5bac-9ec6-df0f2b184b7a
-- title:
--   Uₚ plus cross map equals degeneracy composite on glued Pic⁰
-- statement:
--   Throughout, $p$ is a prime, $M$ is a positive integer divisible by $p$ with $M/p$ also nonzero, and $H$ is a subgroup of $(\mathbb Z/M)^\times$; `hj` asserts that the $q$-expansion `jqModC ℚ` of $j$ lies in the level-one function field `qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))`. The datum $\mathfrak X$ is an `XHDRModelAtP p M H hpM hj`, the integral model package at $p$ for level $\Gamma_H(M)$: it bundles the two-chart model `X p (ΓM M H) hj` over `Spec (R p)` with its properness, flatness, integrality and normality, the smooth level-$\Gamma_N$ model, a curve model `𝔛.Meta` over $\overline{\mathbb Q}$ of the function field `xHFunctionFieldBar M H` together with the isomorphism `𝔛.eeta` onto the generic fibre and its Galois compatibility, the degeneracy morphisms `𝔛.π`, `𝔛.πw`, the involution `𝔛.w`, the diamond isomorphisms `𝔛.dia0`, the smooth locus `𝔛.smoothLocus`, and the fibre data `𝔛.Mfib`, `𝔛.efib`, `𝔛.comp`.
--
--   Further, $A$ is a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (`A.LiesOverPrime p`), whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. $\Lambda$ is a `JHNeronObjectAtP.LevelData p M H hpM A`: a structure morphism `Λ.σA : Spec A ⟶ base p` with `barPt A ≫ Λ.σA = genPt p`, a scheme `Λ.X` with morphism `Λ.f` to `base p`, a relative group law, a bijection `Λ.pts` from $J_H(M/p)$ at the subgroup `infSubgroup p M H hpM` (that is, the degree-zero class group of `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` over $\overline{\mathbb Q}$) onto the sections of `Λ.f` over `genPt p`, and a bijection `Λ.ptsSp` from `Pic0 κ (Fbar p M H hpM κ)` onto the sections of `Λ.f` over `resPt A ≫ Λ.σA`, where `Fbar p M H hpM κ` is the function field `qExpFunctionFieldC κ (ΓN p M H hpM)`. $O$ is a `JHNeronObjectAtP p M H hpM A hA Λ`: a scheme `O.G` with morphism `O.g` to `base p`, a commutative relative group law, a bijection `O.pts` from $J_H(M) =$ `Pic0 (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)` onto the sections of `O.g` over `genPt p` compatible with addition and with the Galois action, the Hecke endomorphisms `O.hecke S t` indexed by the generators [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13), the various geometric properties of `O.g`, the gluing set `O.ssFinset` of pairs of places of `Fbar p M H hpM κ`, the bijection `O.ptsSp` from `GluedPic0 κ (Fbar p M H hpM κ) O.ssFinset` onto the sections of `O.g` over `resPt A ≫ Λ.σA`, the degeneracy homomorphisms `O.degPts` on points and the degeneracy morphism `O.degeneracyHom`. Finally $\rho :$ `R p` $\to A$ is a ring homomorphism with `A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)`, and `hσA` identifies `Λ.σA` with `Spec.map (CommRingCat.ofHom ρ)`.
--
--   The hypotheses fall into the following groups.
--
--   (1) The level-$M$ reduction dictionary `hsp`. For every $i \in \{0,1\}$, every pair of $\overline{\mathbb Q}$-points $y_1, y_2$ of `𝔛.Meta.C` over `𝔛.Meta.toBase`, every pair of sections $u_1, u_2$ of `toBase p (ΓM M H) hj` over `Spec.map (CommRingCat.ofHom ρ)` such that `barPt A` followed by $u_j$ equals $y_j$ followed by `𝔛.eeta ≫ pullback.fst _ _` and such that the image of the underlying map of $u_j$ lies in `𝔛.smoothLocus`, every pair of morphisms $u_{\kappa,1}, u_{\kappa,2}$ from `Spec κ` to the fibre of the level-$\Gamma_M$ model along `(residue ↥A).comp ρ` satisfying $u_{\kappa,j} \circ$ followed by `pullback.fst` equals `Spec.map (CommRingCat.ofHom (residue ↥A))` followed by $u_j$ and $u_{\kappa,j}$ followed by `pullback.snd` equal to the identity, every pair of closed points $P_1, P_2$ of `(𝔛.Mfib A hA ρ hρ).C` whose images under `𝔛.efib A hA ρ hρ` followed by `𝔛.comp A hA ρ hρ i` are the images of the closed point of $\kappa$ under $u_{\kappa,1}$, $u_{\kappa,2}$ respectively, every degree-zero divisor $D_v$ on `xHFunctionFieldBar M H` over $\overline{\mathbb Q}$ equal to `Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1`, and every admissible gluing datum $x$ for `O.ssFinset` whose first divisor component is $[P_1]-[P_2]$ (through `(𝔛.Mfib A hA ρ hρ).placeOfPoint`) if $i = 0$ and $0$ otherwise, whose second divisor component is $[P_1]-[P_2]$ if $i = 1$ and $0$ otherwise, and whose unit component is $0$: there exists a section $s$ of `O.g` over `Λ.σA` with `(O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1` and with `O.ptsSp.symm` of the restriction of $s$ along `resPt A` equal to `GluedPic0.mk O.ssFinset x`.
--
--   (2) The level-$(M/p)$ reduction dictionary `hspΛ`, of the same shape but without any smooth-locus requirement and with the closed points $Q_1, Q_2$ of `(𝔛.Mfib A hA ρ hρ).C` pinned by the condition that their images under `𝔛.efib A hA ρ hρ` are the images of the closed point of $\kappa$ under $u_{\kappa,j}$ followed by the fibre map of `𝔛.π` if $i = 0$ and of `𝔛.πw` otherwise; given in addition a degree-zero divisor $D_v$ on `xHFunctionFieldBar M H` equal to $[y_1]-[y_2]$ and a degree-zero divisor $D_w$ on `Fbar p M H hpM κ` equal to $[Q_1]-[Q_2]$, there exists a section $s_0$ of `Λ.f` over `Λ.σA` with `(Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1` and with `Λ.ptsSp.symm` of the restriction of $s_0$ along `resPt A` equal to `Pic0.mk Dw`.
--
--   (3) The diamond compatibility `hdia0`: for every unit $e$ of $\mathbb Z/(M/p)$ and every closed point $P$ of `(𝔛.Mfib A hA ρ hρ).C`, the image of $P$ under `𝔛.efib A hA ρ hρ`, then the fibre map of the diamond isomorphism `overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)`, then the inverse of `𝔛.efib A hA ρ hρ`, is again a closed point, and its place equals the semilinear automorphism `SemilinearAut.ofAlgAut (diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e))` applied to the place of $P$.
--
--   (4) Frobenius data: three additive endomorphisms $F$, $F^{\mathrm{inv}}$, $F^{*}$ of `Pic0 κ (Fbar p M H hpM κ)` with $F$ given by `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p` (`hF`), the two identities `F.comp Finv = id` and `Finv.comp F = id` (`hFinv`), and $F^{*}z = p \cdot F^{\mathrm{inv}}z$ for all $z$ (`hFstar`).
--
--   (5) Diamond-at-$p$ data: a unit `pb` of $\mathbb Z/(M/p)$ whose underlying residue is $p$ (`hpb`), and an additive endomorphism $\delta$ of `Pic0 κ (Fbar p M H hpM κ)` given by the action of `SemilinearAut.ofAlgAut (diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb))` (`hδ`).
--
--   (6) Degeneracy pull-back data: additive maps `αpull i : JH (M / p) (infSubgroup p M H hpM) →+ JH M H` and morphisms `degPull i : Λ.X ⟶ O.G` over `base p` for $i \in \{0,1\}$, subject to: `hpull`, that `(O.pts (αpull i x)).1` equals `(Λ.pts x).1` followed by `degPull i` for all $x$; `hpull_mul`, that for every test scheme $T$, every $s : T \to$ `base p` and all sections $x, y$ of `Λ.f` over $s$, composing the product `Λ.L.mul s x y` with `degPull i` gives the product `O.L.mul s` of the two composites; and `hpullsp`, that for every section $x$ of `Λ.f` over `resPt A ≫ Λ.σA`, the image under `GluedPic0.toPic0Pair O.ssFinset` of `O.ptsSp.symm` applied to $x$ followed by `degPull i` equals $(z, F^{*}z)$ when $i = 0$ and $(F^{*}z, \delta z)$ when $i = 1$, where $z =$ `Λ.ptsSp.symm x`.
--
--   (7) Atkin–Lehner data: an additive endomorphism $\bar W$ of $J_H(M)$, a semilinear automorphism `wgen` of `xHFunctionFieldBar M H` over $\overline{\mathbb Q}$ with $\bar W x =$ `wgen` $\cdot\, x$ (`hWbar`), and `hwgen`, that whenever two $\overline{\mathbb Q}$-points $y, y'$ satisfy that $y'$ followed by `𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom` equals $y$ followed by `𝔛.eeta ≫ pullback.fst _ _`, then `𝔛.Meta.pointEquivPlace y'` equals `wgen` acting on `𝔛.Meta.pointEquivPlace y`.
--
--   (8) The generic $U_p$ identity: a set $S$ of natural numbers and `hUPgen`, stating that for every $x \in J_H(M)$, `genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) x + Wbar x = αpull 1 (O.degPts 0 x)`.
--
--   (9) Cross data: `hss`, that `O.ssFinset` is cross-stable for the pair consisting of the diamond automorphism `SemilinearAut.ofAlgAut (diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb))` and $1$, i.e. for every $s$ in `O.ssFinset` the pair $(s_2, g_0 \cdot s_1)$ again lies in `O.ssFinset`; and `hβ`, that the base automorphism of that diamond automorphism agrees with the base automorphism of $1$, i.e. it is the identity on $\kappa$.
--
--   Conclusion: for every glued class $\xi$ in `GluedPic0 κ (Fbar p M H hpM κ) O.ssFinset`,
--   $$\mathtt{O.ptsSp}^{-1}\bigl(\mathtt{O.ptsSp}\,\xi \text{ followed by } \mathtt{O.hecke}\,S\,(\mathtt{Gen.U}\,p)\bigr) \; + \; \mathtt{GluedPic0.crossMap}\,\mathtt{O.ssFinset}\,g_0\,1\,\mathtt{hss}\,\mathtt{hβ}\,\xi \; = \; \mathtt{O.ptsSp}^{-1}\bigl(\mathtt{O.ptsSp}\,\xi \text{ followed by } \mathtt{O.degeneracyHom}\,0 \text{ followed by } \mathtt{degPull}\,1\bigr),$$
--   where $g_0$ is the diamond automorphism `SemilinearAut.ofAlgAut (diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb))` and `GluedPic0.crossMap` is the endomorphism of the glued class group attached to the cross-stable pair $(g_0, 1)$ with equal base automorphisms.
--
--   This is the $U_p$ decomposition on the special fibre of the Néron model of $J_H(M)$ at a prime $p$ exactly dividing $M$: read through the dictionary `O.ptsSp` between glued divisor classes on the Deligne–Rapoport special fibre and sections of the Néron model, the Hecke operator $U_p$ plus the Atkin–Lehner cross term equals the composite of the first degeneracy push-forward with the second degeneracy pull-back. It is the form in which the identity is applied by [`ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_mk_eq_mk_frobPullback_and_exists_mk_eq_of_snd_eq_zero`](thm.html#ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_mk_eq_mk_frobPullback_and_exists_mk_eq_of_snd_eq_zero), from which the descriptions of $U_p$ on node units and on the abelian quotient of the special fibre are extracted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicCurve_GluedPic0CrossFunctionality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_add_crossMap_eq_ptsSp_symm_degeneracyHom_degPull
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
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

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

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

    (hss : SemilinearAut.IsCrossStable O.ssFinset
      (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb))) 1)
    (hβ : SemilinearAut.baseAut
        (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb))) =
      SemilinearAut.baseAut (1 : SemilinearAut (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) :
    ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) +
        GluedPic0.crossMap O.ssFinset
          (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb))) 1 hss hβ ξ =
      O.ptsSp.symm (schemeHomOverComp (schemeHomOverComp (O.ptsSp ξ) (O.degeneracyHom 0)) (degPull 1)) := by sorry
