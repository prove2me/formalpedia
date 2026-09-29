-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_toPic0Pair_ptsSp_symm_hecke_U_eq_blockOp
-- name    : ModularCurve.JHNeronObjectAtP.toPic0Pair_ptsSp_symm_hecke_U_eq_blockOp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/ad4e2705-0378-512b-8c4f-d0646ec5ccd5
-- title:
--   Block form of Uₚ on the glued Pic⁰ pair
-- statement:
--   Fix a prime $p$, a nonzero level $M$ with $p \mid M$ and $M/p$ nonzero, and a subgroup $H \le (\mathbb{Z}/M)^\times$; let `hj` record that the $q$-expansion `jqModC ℚ` of $j$ lies in the function field `qExpFunctionFieldC ℚ ⊤` of the curve of full level $\mathrm{SL}_2(\mathbb{Z})$, and let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over $R\,p$: this packages properness, flatness, integrality and local finite presentation of `toBase p (ΓM M H) hj`, integral closedness on affine opens, properness and relative smoothness of dimension $1$ at level `ΓN p M H hpM`, a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` together with the isomorphism `eeta` onto the geometric generic fibre and its Galois equivariance, the pinning of the chart algebra under `Meta.ffEquiv`, and further data for the special fibre (the fibre curve model `Mfib`, its comparison map `efib`, the component maps `comp`, the degeneracy maps `π`, `πw`, the Atkin–Lehner involution `w`, the diamond automorphisms `dia0` and the smooth locus `smoothLocus`).
--
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Let $\Lambda$ be a `JHNeronObjectAtP.LevelData p M H hpM A`, consisting of a section `σA : Spec A ⟶ base p` with `barPt A ≫ σA = genPt p`, a scheme $X$ with structure morphism $f$ over `base p`, a relative group law, a bijection `Λ.pts` from $J_H(M/p)$ at level `infSubgroup p M H hpM` onto the sections of $f$ along `genPt p`, and a bijection `Λ.ptsSp` from $\mathrm{Pic}^0(\kappa, \mathrm{Fbar}\,p\,M\,H\,hpM\,\kappa)$ onto the sections of $f$ along `resPt A ≫ σA`, where `Fbar p M H hpM κ` is the function field `qExpFunctionFieldC κ (ΓN p M H hpM)`. Let $O$ be a `JHNeronObjectAtP p M H hpM A hA Λ`: a smooth, separated, surjective commutative relative group scheme $g : G \to$ `base p` with fibrewise preconnectedness and the further properties listed in that structure, a bijection `O.pts` from $J_H(M)$ onto the sections of $g$ along `genPt p` compatible with addition and with the Galois action, Hecke endomorphisms `O.hecke S t` of $g$ over `base p` compatible with the group law and with `genOpH M H S t` on points, a finite set `O.ssFinset` of pairs of places, a special-fibre dictionary `O.ptsSp` between `GluedPic0 κ (Fbar p M H hpM κ) O.ssFinset` and the sections of $g$ along `resPt A ≫ Λ.σA`, and degeneracy push-forwards `O.degPts i` $: J_H(M) \to J_H(M/p)$. Finally let $\rho : R\,p \to A$ satisfy `A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)`, and let `hσA` identify `Λ.σA` with `Spec.map (CommRingCat.ofHom ρ)`.
--
--   The hypotheses divide into the following groups, all of which are assumed.
--
--   (i) `hsp`, the generic-to-special dictionary for $O$: for each $i \in \{0,1\}$, each pair of $\overline{\mathbb{Q}}$-points $y_1, y_2$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, each pair of lifts $u_1, u_2$ over `Spec.map (CommRingCat.ofHom ρ)` of the structure morphism `toBase p (ΓM M H) hj` whose restriction along `barPt A` agrees with $y_1$, resp. $y_2$, followed by `eeta` and the first pullback projection, and whose topological image lies in `𝔛.smoothLocus`, each pair of fibre sections $u_{\kappa,1}, u_{\kappa,2}$ of the fibre of `toBase p (ΓM M H) hj` along `(IsLocalRing.residue ↥A).comp ρ` reducing $u_1$, resp. $u_2$, and splitting the fibre structure morphism, and each pair of closed points $P_1, P_2$ of `(𝔛.Mfib A hA ρ hρ).C` whose images under `𝔛.efib` followed by `𝔛.comp … i` are the closed points of $u_{\kappa,1}$, resp. $u_{\kappa,2}$: given a degree-zero divisor $Dv$ on `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ equal to $\mathrm{single}(\mathrm{place}(y_1)) - \mathrm{single}(\mathrm{place}(y_2))$ under `𝔛.Meta.pointEquivPlace`, and an admissible glueing datum $x$ for `O.ssFinset` whose first divisor component is $\mathrm{single}(\mathrm{place}(P_1)) - \mathrm{single}(\mathrm{place}(P_2))$ if $i = 0$ and $0$ otherwise, whose second divisor component is that same difference if $i = 1$ and $0$ otherwise, and whose unit component vanishes, there exists a section $s$ of `O.g` over `Λ.σA` with `(O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1` and with `O.ptsSp.symm` of the restriction of $s$ along `resPt A` equal to `GluedPic0.mk O.ssFinset x`.
--
--   (ii) `hspΛ`, the corresponding dictionary for $\Lambda$: for each $i \in \{0,1\}$, points $y_1, y_2$, lifts $u_1, u_2$ (here without the smooth-locus condition), fibre sections $u_{\kappa,1}, u_{\kappa,2}$ as above, and closed points $Q_1, Q_2$ of `(𝔛.Mfib A hA ρ hρ).C` whose images under `𝔛.efib` are the closed points of $u_{\kappa,1}$, resp. $u_{\kappa,2}$, transported by the fibre of `𝔛.π` when $i = 0$ and of `𝔛.πw` otherwise, and given degree-zero divisors $Dv = \mathrm{single}(\mathrm{place}(y_1)) - \mathrm{single}(\mathrm{place}(y_2))$ on `xHFunctionFieldBar M H` and $Dw = \mathrm{single}(\mathrm{place}(Q_1)) - \mathrm{single}(\mathrm{place}(Q_2))$ on `Fbar p M H hpM κ`, there exists a section $s_0$ of `Λ.f` over `Λ.σA` with `(Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1` and `Λ.ptsSp.symm` of the restriction of $s_0$ along `resPt A` equal to `Pic0.mk Dw`.
--
--   (iii) `hdia0`, the diamond dictionary on the special fibre: for every unit $e$ of $\mathbb{Z}/(M/p)$ and every closed point $P$ of `(𝔛.Mfib A hA ρ hρ).C`, the point obtained from $P$ by applying `𝔛.efib`, the fibre of the automorphism `𝔛.dia0 e`, and the inverse of `𝔛.efib` is again closed, and its place is the place of $P$ moved by the semilinear automorphism attached to `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e)`.
--
--   (iv) Frobenius data: additive endomorphisms $F$, $F^{\mathrm{inv}}$, $F^{*}$ of $\mathrm{Pic}^0(\kappa, \mathrm{Fbar}\,p\,M\,H\,hpM\,\kappa)$ with $F$ equal to `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p` pointwise, $F \circ F^{\mathrm{inv}} = \mathrm{id}$ and $F^{\mathrm{inv}} \circ F = \mathrm{id}$, and $F^{*}z = p \cdot F^{\mathrm{inv}}z$ for all $z$.
--
--   (v) Diamond operator data: a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$, and the additive endomorphism $\delta$ acting as the semilinear automorphism attached to `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`.
--
--   (vi) Degeneracy data: additive maps `αpull i : JH (M / p) (infSubgroup p M H hpM) →+ JH M H` and morphisms `degPull i` from `Λ.f` to `O.g` over `base p`, for $i \in \{0,1\}$, with `hpull` asserting $(O.\mathrm{pts}(\alpha_{\mathrm{pull}}^i x)).1 = (\Lambda.\mathrm{pts}\,x).1$ followed by `(degPull i).1` for all $x$, and `hpullsp` asserting that for every section $x$ of `Λ.f` along `resPt A ≫ Λ.σA` the pair `GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i)))` equals $(\Lambda.\mathrm{ptsSp}^{-1}x,\; F^{*}(\Lambda.\mathrm{ptsSp}^{-1}x))$ when $i = 0$ and $(F^{*}(\Lambda.\mathrm{ptsSp}^{-1}x),\; \delta(\Lambda.\mathrm{ptsSp}^{-1}x))$ when $i = 1$.
--
--   (vii) Atkin–Lehner data: an additive endomorphism $\overline{W}$ of $J_H(M)$ and a semilinear automorphism `wgen` of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ with $\overline{W}x = \mathrm{wgen} \cdot x$ for all $x$, together with `hwgen`: whenever two $\overline{\mathbb{Q}}$-points $y, y'$ of `𝔛.Meta.C` satisfy $y'$ followed by `eeta`, the first projection and `𝔛.w.hom` equals $y$ followed by `eeta` and the first projection, the place of $y'$ is `wgen` applied to the place of $y$.
--
--   (viii) The generic identity `hUPgen` for a set of primes $S$: for every $x \in J_H(M)$,
--   $$\mathrm{genOpH}\,M\,H\,S\,(U_p)\,x + \overline{W}x = \alpha_{\mathrm{pull}}^1(O.\mathrm{degPts}\,0\,x),$$
--   where $U_p$ is the generator `CohCarrier.Gen.U p _ hpM`, so that `genOpH` is the Hecke operator `heckeOperatorHAlong (AlgebraicClosure ℚ) M H p`.
--
--   Under these hypotheses the conclusion is: for every $\xi$ in `GluedPic0 κ (Fbar p M H hpM κ) O.ssFinset`,
--   $$\mathrm{toPic0Pair}\,\bigl(O.\mathrm{ptsSp}^{-1}(\mathrm{schemeHomOverComp}\,(O.\mathrm{ptsSp}\,\xi)\,(O.\mathrm{hecke}\,S\,U_p))\bigr) = \mathrm{blockOp}\;F^{*}\;((p-1)\cdot\mathrm{id})\;0\;(\delta \circ F)\,\bigl(\mathrm{toPic0Pair}\,\xi\bigr),$$
--   that is: transporting $\xi$ to a section of `O.g` along `resPt A ≫ Λ.σA`, composing with the Hecke endomorphism attached to $U_p$, transporting back, and taking the pair of divisor classes given by `GluedPic0.toPic0Pair` (the classes of the two divisor components of an admissible glueing datum) yields, on the pair $(a,b) = \mathrm{toPic0Pair}\,\xi$, the pair $(F^{*}a + (p-1)b,\; \delta(F b))$, with $F^{*} = p\,F^{-1}$ by (iv). Only the abelian-quotient pair of divisor classes is asserted; no statement is made about the unit component of the glueing datum.
--
--   This is the computation of the action of $U_p$ on the special fibre at a prime $p$ exactly dividing the level, in the Deligne–Rapoport description of the reduction of $X_H(M)$ by two copies of the curve of level $M/p$ glued at supersingular points: on the pair of $\mathrm{Pic}^0$-components of the glued class group the operator is block upper-triangular, with diagonal entries $p\,F^{-1}$ and $\langle p\rangle_* F$. It is used in the analysis of the $p$-adic Tate module and the inertia invariants of $J_H(M)$ at $p$ that underlies level lowering, and is cited in the vanishing criterion for sections of the Néron object whose second block-component is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_toPic0Pair_ptsSp_symm_hecke_U_eq_blockOp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.JHNeronObjectAtP.toPic0Pair_ptsSp_symm_hecke_U_eq_blockOp
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
    :

    (      ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
        GluedPic0.toPic0Pair O.ssFinset
            (O.ptsSp.symm (schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) =
          AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F)
            (GluedPic0.toPic0Pair O.ssFinset ξ)) := by sorry
