-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_slopeLaw_isUnit_ord_eq_zero_at_crossing_of_dvd_width
-- name    : ModularCurve.XHDRModelAtP.exists_section_slopeLaw_isUnit_ord_eq_zero_at_crossing_of_dvd_width
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/d3f77694-675d-5c00-944d-9952472a73cb
-- title:
--   Local section cutting k times a branch at a crossing
-- statement:
--   Arithmetic level data. Fixed throughout are a prime $p$ and a nonzero natural number $M$ with $p \mid M$ (`hpM`) but $p^2 \nmid M$ (`hpM2`), a subgroup $H \le (\mathbb Z/M)^\times$ which (`hHp`) contains every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$, with $M/p$ nonzero, the hypothesis `hj` that the $q$-series `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤`, and a datum $\mathfrak X$ of type `XHDRModelAtP p M H hpM hj`. The latter bundles a Deligne–Rapoport-style integral model: the structure map `toBase p (ΓM M H) hj` of `X p (ΓM M H) hj` over `Spec (CommRingCat.of (R p))` is proper, flat and locally of finite presentation with integral source and with integrally closed sections on affine opens, the level-`ΓN p M H hpM` structure map is proper and smooth of relative dimension $1$, a curve model `𝔛.Meta` over $\overline{\mathbb Q}$ with function field `xHFunctionFieldBar M H` (the base change to $\overline{\mathbb Q}$ of the Laurent-series realisation `xHFunctionField M H` of the function field of $X_H(M)$) is given together with an isomorphism `𝔛.eeta` onto the base change of the model along $R p \to \overline{\mathbb Q}$ compatible with the structure maps, and Galois-equivariance and chart-normalisation clauses; among its further fields are the map `𝔛.w`, the special-fibre curve model `𝔛.Mfib`, the maps `𝔛.efib` and `𝔛.comp _ _ _ _ i` ($i \in \{0,1\}$) exhibiting the two components of the fibre, and the identification `𝔛.nodeEquiv` of the crossings with supersingular places, through which `𝔛.placeOn0` and `𝔛.placeOn1` are defined by `placeOn1 n = 𝔛.nodeEquiv n` and `placeOn0 n = qExpFrobeniusPlaceModL _ (ΓN p M H hpM) p (𝔛.nodeEquiv n)`.
--
--   The place. Further fixed are a valuation subring $A$ of $\overline{\mathbb Q}$ with `A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, whose residue field $\kappa :=$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed, and a ring homomorphism $\rho : R p \to A$ with $A.\mathrm{subtype} \circ \rho$ equal to the structure map $R p \to \overline{\mathbb Q}$ (`hρ`). Write $X_A$ for the pullback of `toBase p (ΓM M H) hj` along `Spec.map ρ`, and $F_\kappa :=$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)`.
--
--   Diamond operator and node pairs. A unit $pb$ of $\mathbb Z/(M/p)$ with underlying element $p$ (`hpb`) is given, together with a self-map $\delta$ of the set of places of $F_\kappa$ over $\kappa$ which (`hδ`) acts as the semilinear automorphism attached by `SemilinearAut.ofAlgAut` to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36), where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb Z/(M/p))^\times$. A finite set $SS$ of pairs of places of $F_\kappa$ is given whose members are exactly (`hSS`) the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is the pairs $s$ with $s.2$ a supersingular place and $s.1 =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` $s.2$.
--
--   Specialisation data. Given are an $\overline{\mathbb Q}$-algebra automorphism $\theta$ of $FM :=$ `xHFunctionFieldBar M H`, an integral $\overline{\mathbb Q}$-algebra map $\alpha$ from $FMp :=$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` to $FM$ (`hα`) with $\beta := \theta \circ \alpha$ also integral (`hβ`), a specialisation packet $Psp$ of type `JHPlaceSpecialization p M H hpM A` (a map `sp` from places of $FMp$ over $\overline{\mathbb Q}$ to places of $F_\kappa$ over $\kappa$ together with a map on degree-zero divisor classes, surjectivity of `sp`, the divisor/$q$-expansion compatibilities, invariance under the inertia subgroup of $A$ and Frobenius-equivariance), and a prolongation datum $Rpd$ of type `JHPlaceSpecialization.ProlongationDatum Psp θ`, consisting of two regular prolongations $R_1, R_2$ of $A$ to $FM$ with residue values in $F_\kappa$, the $q$-expansion compatibility of $R_1$'s residue, and the identification of $R_2$ with $R_1$ twisted by $\theta$. Recall `Psp.reduceFst α hα W = Psp.sp (W.restrictAlong α hα)` and `Psp.reduceSnd β hβ δ W = δ (Psp.sp (W.restrictAlong β hβ))`.
--
--   The hypothesis `hwgen` states that for two $\overline{\mathbb Q}$-points $y, y'$ of `𝔛.Meta.C` over the base, if $y'$ followed by `𝔛.eeta`, the first projection and `𝔛.w.hom` agrees with $y$ followed by `𝔛.eeta` and the first projection, then `𝔛.Meta.pointEquivPlace y'` is the image of `𝔛.Meta.pointEquivPlace y` under the semilinear automorphism attached to $\theta$. The hypothesis `hα_coe` states that $\alpha$ is the identity on underlying Laurent series. The hypothesis `hTD` is `Psp.TypeDichotomy α β hα hβ δ`: for every place $W$ of $FM$, either `reduceFst W` is the Frobenius pullback of `reduceSnd W`, or $\delta$ applied to the Frobenius pullback of `reduceFst W` equals `reduceSnd W`. The hypothesis `hmodel` is `Rpd.IsModel α β hα hβ δ`, the conjunction of the four laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty`, `CuspLawZero`.
--
--   Two compatibility blocks are assumed, each quantified over an index $i \in \{0,1\}$, a $\overline{\mathbb Q}$-point $y$ of `𝔛.Meta.C` over the base, a lift $u$ of the model to $X_A$ over `Spec.map ρ` with `barPt A` followed by $u$ equal to $y$ followed by `𝔛.eeta` and the first projection, a $\kappa$-section $u\kappa$ of the fibre `fibre ((residue ↥A).comp ρ)` satisfying the two stated projection identities, and a closed point $P_0$ of `(𝔛.Mfib A hA ρ hρ).C` whose image under `𝔛.efib` followed by `𝔛.comp _ i` is the image of the closed point under $u\kappa$. Under these, `hcompat` asserts that `(𝔛.Mfib A hA ρ hρ).placeOfPoint P₀` equals `Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)` if $i = 0$ and `Psp.reduceSnd β hβ δ (𝔛.Meta.pointEquivPlace y)` otherwise, while `hcompat'` asserts the crossed relations: for $i = 0$, `Psp.reduceSnd β hβ δ (𝔛.Meta.pointEquivPlace y)` equals $\delta$ of the Frobenius pullback `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` of `(𝔛.Mfib A hA ρ hρ).placeOfPoint P₀`, and for $i = 1$, `Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)` equals that Frobenius pullback.
--
--   Annulus block. Given are widths $e : SS \to \mathbb N$ with $e(s) > 0$ (`he`) and annuli $An(s)$ of type [`AlgebraicCurve.Annulus A FM`](def/AlgebraicCurve_SemistableCharts.html#L86) — each consisting of a set `dom` of places of $FM$, a parameter `param`, a modulus in the maximal ideal of $A$, and the structural axioms: the places in `dom` are rational, `param` is integral at them with value in the maximal ideal of $A$, nonzero, and dividing the modulus; the value of `param` determines the place in `dom` uniquely; `ord_P(param − param(P)) = 1`; and the unit principle. The hypothesis `hAn` requires for each $s$ the following seven clauses: (1) `dom (An s)` is exactly the set of places $W$ of $FM$ with `Psp.reduceFst α hα W = s.1.1` and with neither `Psp.IsStrictFst α β hα hβ δ W` nor `Psp.IsStrictSnd α β hα hβ δ W` holding, where `IsStrictFst W` means that $\delta$ of the Frobenius pullback of `reduceFst W` equals `reduceSnd W` while `reduceFst W` does not satisfy the predicate `Fixed` for $\delta$, and `IsStrictSnd W` means that `reduceFst W` is the Frobenius pullback of `reduceSnd W` while `reduceSnd W` does not satisfy `Fixed`; (2) the modulus of $An(s)$ is $p^{e(s)}$ times a unit of $A$; (3) the parameter is fixed by `arithmeticGalois (xHFunctionField M H) σ` for every $\sigma$ in `A.inertiaSubgroupIn ℚ`; (4) the product of the inverse of the modulus with the parameter lies in `Rpd.R₁.integers`; (5) the parameter lies in `Rpd.R₂.integers` and its $R_2$-residue is nonzero; (6) the parameter lies in `Rpd.R₂.integers`, its $R_2$-residue has $\mathrm{ord}$ equal to $1$ at the place $s.1.2$, and for every $f \in$ `Rpd.R₂.integers` with nonzero $R_2$-residue and with $\mathrm{ord}_P f = 0$ for all $P \in$ `dom (An s)`, one has for every such $P$ that $f(P)\cdot (\mathrm{param}(P))^{-\mathrm{ord}_{s.1.2}(R_2\text{-residue of } f)}$ lies in $A$ and is a unit there; (7) the element $(\text{modulus}) \cdot (\text{param})^{-1}$ lies in `Rpd.R₁.integers`, its $R_1$-residue has $\mathrm{ord}$ equal to $1$ at the place $s.1.1$, and the same unit normalisation holds with $R_1$, $s.1.1$ and this element in place of $R_2$, $s.1.2$ and the parameter. Finally a natural number $k$ is given with $e(s) \mid k$ for all $s \in SS$ (`hk`).
--
--   Pinning of the charts. A morphism `gA` from `𝔛.Meta.C` to $X_A$ is given whose first projection agrees with `𝔛.eeta` followed by the first projection (`hgA₁`) and whose second projection is `𝔛.Meta.toBase` followed by `barPt A` (`hgA₂`), and a morphism `bc` from `fibre ((residue ↥A).comp ρ)` to $X_A$ compatible with the first projections (`hbc₁`) and with the second projections up to `Spec.map (residue ↥A)` (`hbc₂`).
--
--   Conclusion. For every $s \in SS$ and every point $n$ of the pullback of `𝔛.comp A hA ρ hρ 0` along `𝔛.comp A hA ρ hρ 1` — a crossing of the two components of the special fibre — such that `𝔛.placeOn0 A hA ρ hρ n = s.1.1` and `𝔛.placeOn1 A hA ρ hρ n = s.1.2`, there exist an open subset $U$ of $X_A$ containing the image under `bc` of the point of the fibre underlying $n$ (via the first projection followed by `𝔛.comp _ 0`), a proof that the open subscheme `gA ⁻¹ᵁ U` is nonempty, and a section $t \in \Gamma(X_A, U)$ with the following four properties, where $T$ denotes the element of $FM$ obtained from $t$ by pulling back along `gA`, taking the germ at the generic point of `𝔛.Meta.C` and transporting along `𝔛.Meta.ffEquiv.symm`:
--
--   (i) there is a nonzero $a \in \overline{\mathbb Q}$ such that for every $P \in$ `dom (An s)` one has $\mathrm{ord}_P T = 0$, and $T(P)\cdot a\cdot(\mathrm{param}(P))^{-k/e(s)}$ (the exponent being the negative of the natural-number quotient $k/e(s)$) lies in $A$ and is a unit there;
--
--   (ii) for every closed point $Q$ of `(𝔛.Mfib A hA ρ hρ).C` whose image under `𝔛.efib` followed by `𝔛.comp _ 1` and then `bc` lies in $U$ and differs from the image of the crossing, the germ of $t$ at that point is a unit;
--
--   (iii) for every closed point $Q$ of `(𝔛.Mfib A hA ρ hρ).C` whose image under `𝔛.efib` followed by `𝔛.comp _ 0` and then `bc` lies in $U$ and differs from the image of the crossing, there are an open $W \le U$ containing that point and a section $t_0 \in \Gamma(X_A, W)$ with $t|_W = p^k\, t_0$ and with the germ of $t_0$ at that point a unit;
--
--   (iv) for every closed point $x$ of `𝔛.Meta.C` with `gA.base x` in $U$, the order of $T$ at `𝔛.Meta.placeOfPoint x` is $0$.
--
--   The statement provides, at a crossing of the special fibre of the Deligne–Rapoport model of $X_H(M)$ over a place $A$ of $\overline{\mathbb Q}$ above $p$ (with $p$ exactly dividing $M$), a local equation for $k$ times one branch: a section which is a unit along the points of one component, $p^k$ times a unit along the points of the other, has no zeros or poles on the geometric generic fibre over $U$, and on the node annulus is, up to a constant and a unit of $A$, the $k/e(s)$-th power of the annulus parameter. It is used in the annulus-by-annulus construction of good divisors and vertical slopes on the model ([`ModularCurve.XHDRModelAtP.forall_annulus_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_dvd_of_offDiag`](thm.html#ModularCurve.XHDRModelAtP.forall_annulus_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_dvd_of_offDiag)), part of the comparison of the two degeneracy maps at $p$ in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_section_slopeLaw_isUnit_ord_eq_zero_at_crossing_of_dvd_width.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_section_slopeLaw_isUnit_ord_eq_zero_at_crossing_of_dvd_width
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    :
    ∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
      ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U)
        (_ : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (t : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),

        (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0 ∧
            ∃ h : P.evalAt (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) → IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ U _ hQ).hom t)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) →
          ∃ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hWU : W ≤ U) (hQW : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ W) (t₀ : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)),
            (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.map (homOfLE hWU).op t = ((p : ℕ) : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)) ^ k * t₀ ∧
            IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ W _ hQW).hom t₀)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C), gA.base x.1 ∈ U → (𝔛.Meta.placeOfPoint x).ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0) := by sorry
