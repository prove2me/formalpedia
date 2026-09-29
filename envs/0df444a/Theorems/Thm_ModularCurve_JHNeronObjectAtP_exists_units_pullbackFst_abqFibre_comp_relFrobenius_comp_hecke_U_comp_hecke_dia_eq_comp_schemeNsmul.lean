-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul
-- name    : ModularCurve.JHNeronObjectAtP.exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/12d99a72-d86d-5fbe-87bb-9883425ccf54
-- title:
--   Frobenius, Uₚ and a diamond give [p] on ker abq₁
-- statement:
--   Setting. Fix a prime $p$ and $M\ge 1$, a subgroup $H\le(\mathbb Z/M)^\times$, and assume $p\mid M$ (`hpM`) but $p^2\nmid M$ (`hpM2`), so that $p$ exactly divides $M$; `hHp` requires that $H$ contain the whole kernel of the reduction $(\mathbb Z/M)^\times\to(\mathbb Z/(M/p))^\times$, and `infSubgroup p M H hpM` denotes the image of $H$ in $(\mathbb Z/(M/p))^\times$. Let $Pl$ be a valuation subring of $\overline{\mathbb Q}=\mathrm{AlgebraicClosure}\ \mathbb Q$ with `hPl : Pl.LiesOverPrime p`, i.e. $p$ lies in the nonunits of $Pl$, and assume its residue field $\kappa=\mathrm{ResidueField}\ Pl$ has characteristic $p$ and is algebraically closed. The hypothesis `hj` says that the $q$-expansion `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak X$ be an `XHDRModelAtP p M H hpM hj`, i.e. a Deligne–Rapoport-style integral model datum for the modular curve of level $\Gamma_M(M,H)$ over $R_p$, carrying among other things a curve model `𝔛.Meta` of the geometric function field $\overline{F}_H=$`xHFunctionFieldBar M H` over $\overline{\mathbb Q}$ together with the isomorphism `𝔛.eeta` onto the generic geometric fibre, the degeneracy maps `𝔛.π`, `𝔛.πw`, the involution `𝔛.w`, the diamond isomorphisms `𝔛.dia0`, the smooth locus `𝔛.smoothLocus`, and, for the data $(\rho,h\rho)$ below, the special-fibre curve model `𝔛.Mfib`, its comparison `𝔛.efib` and the two maps `𝔛.comp i`.
--
--   Let $\Lambda$ be a `JHNeronObjectAtP.LevelData p M H hpM Pl`: a morphism $\sigma_A:\operatorname{Spec}Pl\to\mathrm{base}\ p$ lying over the generic point, a scheme $\Lambda.X$ with structure morphism $\Lambda.f$ to $\mathrm{base}\ p$, a relative group law $\Lambda.L$ on it, a bijection $\Lambda.\mathrm{pts}$ from $J_H(M/p,\,\mathrm{infSubgroup})=\mathrm{Pic}^0(\overline F_{H'})$ onto the sections of $\Lambda.f$ over the generic point, and a bijection $\Lambda.\mathrm{ptsSp}$ from $\mathrm{Pic}^0_\kappa(\mathrm{Fbar}\ p\ M\ H\ hpM\ \kappa)$ onto the sections over $\mathrm{resPt}\ Pl\ggg\sigma_A$; here $\mathrm{Fbar}$ is the level-$\Gamma_N(p,M,H)$ $q$-expansion function field over $\kappa$. Let $O$ be a `JHNeronObjectAtP p M H hpM Pl hPl Λ`: a scheme $O.G$ with structure morphism $O.g$, a commutative relative group law $O.L$, a bijection $O.\mathrm{pts}$ from $J_H(M,H)$ onto the sections of $O.g$ over the generic point, the smoothness, separatedness, finite-type, quasi-compactness, surjectivity and fibrewise preconnectedness of $O.g$, additivity and Galois equivariance of $O.\mathrm{pts}$, the Hecke endomorphisms $O.\mathrm{hecke}\ S\ t$ over the base for each generator $t$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) together with their additivity and their compatibility with $O.\mathrm{pts}$, flatness and surjectivity of the multiplication maps $O.L.\mathrm{schemeNsmul}\ n$, and the further fields used below, among them the supersingular gluing set $O.\mathrm{ssFinset}$ (a finite set of pairs of places of $\mathrm{Fbar}$), the bijection $O.\mathrm{ptsSp}$ onto the sections over the special point from the glued group $\mathrm{GluedPic0}$ of $O.\mathrm{ssFinset}$, the morphisms $O.\mathrm{abqFibre}\ i$ and the homomorphisms $O.\mathrm{degPts}\ i:J_H(M,H)\to J_H(M/p,\mathrm{infSubgroup})$. The hypothesis `hrep` asserts that the relative Picard functor of $\mathfrak X$'s model, cut out by the fibrewise-algebraically-equivalent-to-zero condition `algEquivZeroCut`, is represented by the designation built from $O.G$, $O.g$ and the unit section of $O.L$ at the identity. A set of primes $S$ is fixed, and $M/p$ is nonzero.
--
--   Arithmetic of the base. A ring homomorphism $\rho:R_p\to Pl$ is given with $Pl.\mathrm{subtype}\circ\rho=$ the structure map $R_p\to\overline{\mathbb Q}$ (`hρ`), and `hσA` identifies $\Lambda.\sigma_A$ with $\operatorname{Spec}$ of $\rho$.
--
--   Specialisation hypotheses. `hsp` (a long list of binders, summarised here) requires, for each $i\in\{0,1\}$: given two $\overline{\mathbb Q}$-points $y_1,y_2$ of `𝔛.Meta` over its base, $Pl$-points $u_1,u_2$ of the model lying over $\operatorname{Spec}\rho$ whose composites with $\mathrm{barPt}\ Pl$ are the images of $y_1,y_2$ and whose set-theoretic images lie in $\mathfrak X.\mathrm{smoothLocus}$, $\kappa$-points $u_{\kappa 1},u_{\kappa 2}$ of the fibre over the residue map composed with $\rho$ reducing $u_1,u_2$ and splitting the fibre structure map, closed points $P_1,P_2$ of $(\mathfrak X.\mathrm{Mfib})$'s curve whose images under $\mathfrak X.\mathrm{efib}$ followed by $\mathfrak X.\mathrm{comp}\ i$ are the closed points of $u_{\kappa 1},u_{\kappa 2}$, a degree-zero divisor $Dv$ on $\overline F_H$ equal to $[\,y_1\,]-[\,y_2\,]$ under the point–place bijection of `𝔛.Meta`, and an admissible gluing datum $x$ whose first component is $[\,P_1\,]-[\,P_2\,]$ when $i=0$ and $0$ otherwise, whose second component is $[\,P_1\,]-[\,P_2\,]$ when $i=1$ and $0$ otherwise, and whose third component vanishes: then there is a section $s$ of $O.g$ over $\Lambda.\sigma_A$ with $(O.\mathrm{pts}(\mathrm{Pic0.mk}\ Dv)).1=\mathrm{barPt}\ Pl\ggg s.1$ and $O.\mathrm{ptsSp}^{-1}$ of the composite of $\mathrm{resPt}\ Pl$ with $s$ equal to the class of $x$ in $\mathrm{GluedPic0}$. The hypothesis `hspΛ` (likewise summarised) is the analogous statement one level down: for $i\in\{0,1\}$, points $y_1,y_2$, lifts $u_1,u_2$, reductions $u_{\kappa 1},u_{\kappa 2}$, closed points $Q_1,Q_2$ whose images under $\mathfrak X.\mathrm{efib}$ agree with the images of the closed points under the fibre map of $\mathfrak X.\pi$ (for $i=0$) or $\mathfrak X.\pi_w$ (for $i=1$), a degree-zero divisor $Dv=[\,y_1\,]-[\,y_2\,]$ and a degree-zero divisor $Dw=[\,Q_1\,]-[\,Q_2\,]$ on $\mathrm{Fbar}$, there is a section $s_0$ of $\Lambda.f$ over $\Lambda.\sigma_A$ with $(\Lambda.\mathrm{pts}(O.\mathrm{degPts}\ i\,(\mathrm{Pic0.mk}\ Dv))).1=\mathrm{barPt}\ Pl\ggg s_0.1$ and $\Lambda.\mathrm{ptsSp}^{-1}$ of its reduction equal to $\mathrm{Pic0.mk}\ Dw$.
--
--   Diamonds and Frobenius on the special fibre. `hdia0` says that for every $e\in(\mathbb Z/(M/p))^\times$ and every closed point $P$ of the special-fibre curve, transporting $P$ through $\mathfrak X.\mathrm{efib}$, the fibre map of the isomorphism $\mathfrak X.\mathrm{dia0}\ e$ and the inverse of $\mathfrak X.\mathrm{efib}$ again yields a closed point, whose place is the place of $P$ acted on by the semilinear automorphism attached to $\mathrm{diamondActionModL}\ \kappa\ (M/p)\ \mathrm{infSubgroup}$ at $\mathrm{CuspForm.gammaLift}\ (M/p)\ e$. Three additive endomorphisms $F$, $F^{-1}$, $F^\ast$ of $\mathrm{Pic}^0_\kappa(\mathrm{Fbar})$ are given with $F$ equal to the Frobenius pushforward $\mathrm{qExpFrobeniusPushforwardModL}$ (`hF`), $F^{-1}$ a two-sided inverse of $F$ (`hFinv`), and $F^\ast z=p\cdot F^{-1}z$ (`hFstar`). A unit $pb\in(\mathbb Z/(M/p))^\times$ with underlying element $p$ (`hpb`) is fixed, and $\delta$ is the additive endomorphism given by the diamond action of $\mathrm{gammaLift}\ (M/p)\ pb$ (`hδ`).
--
--   Degeneracy data. Homomorphisms $\alpha_i:J_H(M/p,\mathrm{infSubgroup})\to J_H(M,H)$ and morphisms $\mathrm{degPull}\ i$ from $\Lambda.f$ to $O.g$ over the base are given for $i\in\{0,1\}$, with: `hpull`, $(O.\mathrm{pts}(\alpha_i x)).1=(\Lambda.\mathrm{pts}\ x).1\ggg(\mathrm{degPull}\ i).1$ on generic points; `hpull_mul`, each $\mathrm{degPull}\ i$ carries $\Lambda.L$-multiplication of sections over any base change to $O.L$-multiplication; `hpullsp`, for any section $x$ over $\mathrm{resPt}\ Pl\ggg\Lambda.\sigma_A$, the pair obtained from $O.\mathrm{ptsSp}^{-1}$ of the composite with $\mathrm{degPull}\ i$ by $\mathrm{GluedPic0.toPic0Pair}$ equals $(\Lambda.\mathrm{ptsSp}^{-1}x,\ F^\ast(\Lambda.\mathrm{ptsSp}^{-1}x))$ for $i=0$ and $(F^\ast(\Lambda.\mathrm{ptsSp}^{-1}x),\ \delta(\Lambda.\mathrm{ptsSp}^{-1}x))$ for $i=1$.
--
--   The Atkin–Lehner involution and the Eichler relation. An additive endomorphism $\overline W$ of $J_H(M,H)$ is given, realised as the action of a semilinear automorphism $\mathrm{wgen}$ of $\overline F_H$ over $\overline{\mathbb Q}$ (`hWbar`), and `hwgen` requires that whenever two points $y,y'$ satisfy $y'\ggg\mathfrak X.\mathrm{eeta}\ggg\mathrm{pullback.fst}\ggg\mathfrak X.w$ equal to the image of $y$, their places satisfy $[\,y'\,]=\mathrm{wgen}\cdot[\,y\,]$. The relation `hUPgen` states that for all $x\in J_H(M,H)$, $\mathrm{genOpH}\ M\ H\ S\ (U_p)\,x+\overline W x=\alpha_1(O.\mathrm{degPts}\ 0\ x)$.
--
--   Combinatorial and Frobenius-divisor data. A permutation $\sigma$ of $O.\mathrm{ssFinset}$ is given with $(\sigma n)_2=n_1$ for all $n$ (`hσ`). A permutation $\Phi$ of the places of $\mathrm{Fbar}$ is given, equal to $\mathrm{qExpFrobeniusPlaceModL}$ (the first hypothesis named `hΦ`), and `hFdiv` requires that $F(\mathrm{Pic0.mk}\ D)=\mathrm{Pic0.mk}\ D'$ whenever $D'=\Phi_\ast D$ as divisors. The hypothesis `hpull1sp` requires, for a degree-zero divisor $D$ and an admissible gluing datum $x_1$ such that $D$ and $\Phi_\ast^{-1}$-compatibly $D\circ\Phi$ vanish at both members of every pair in $O.\mathrm{ssFinset}$, that the first component of $x_1$ is $p\cdot(\Phi^{-1})_\ast D$, the second is the diamond action of $\mathrm{gammaLift}\ (M/p)\ pb$ applied to $D$, and the third is $0$; the conclusion is that $O.\mathrm{ptsSp}^{-1}$ of the composite of $\Lambda.\mathrm{ptsSp}(\mathrm{Pic0.mk}\ D)$ with $\mathrm{degPull}\ 1$ is the class of $x_1$.
--
--   Frobenius on the geometric special fibre. Write $Y=\mathrm{RelativeGroupLaw.baseChangeScheme}\ (\mathrm{resPt}\ Pl\ggg\Lambda.\sigma_A)\ O.g$, the fibre product of $O.g$ with $\mathrm{resPt}\ Pl\ggg\Lambda.\sigma_A$. The hypothesis `hp0` says $p=0$ in $\Gamma(Y,\top)$, so that the absolute $p$-power Frobenius $\mathrm{Scheme.frobenius}\ Y\ p\ 1$ is defined, and the last hypothesis, also named `hΦ`, says that this Frobenius followed by $\mathrm{pullback.fst}\ O.g\ (\mathrm{resPt}\ Pl\ggg\Lambda.\sigma_A)$ and then $O.g$ equals $\mathrm{pullback.snd}$ followed by $\mathrm{resPt}\ Pl\ggg\Lambda.\sigma_A$; this is exactly the compatibility needed to lift the absolute Frobenius to an endomorphism $\mathrm{Fr}$ of $Y$ over the base, namely $\mathrm{pullback.lift}$ of the Frobenius composed with $\mathrm{pullback.fst}$ and of $\mathrm{pullback.snd}$.
--
--   Conclusion. There exists $d_0\in(\mathbb Z/M)^\times$ such that the following two morphisms out of $\mathrm{pullback}\,(O.\mathrm{abqFibre}\ 1).1\,((\Lambda.L.\mathrm{baseChange}(\mathrm{resPt}\ Pl\ggg\Lambda.\sigma_A)).\mathrm{one}(\mathbf 1)).1$ — the fibre product of $(O.\mathrm{abqFibre}\ 1).1$ with the unit section of the base-changed group law of $\Lambda$, i.e. the scheme-theoretic kernel of $O.\mathrm{abqFibre}\ 1$ — agree: writing $k_1$ for the first projection of this fibre product into $Y$,
--   $$k_1\ \text{followed by}\ \mathrm{Fr},\ \text{then by the base change to }Y\text{ of }O.\mathrm{hecke}\ S\ (U_p),\ \text{then by the base change to }Y\text{ of }O.\mathrm{hecke}\ S\ (\langle d_0\rangle)$$
--   equals
--   $$k_1\ \text{followed by the base change to }Y\text{ of }O.L.\mathrm{schemeNsmul}\ p .$$
--   Here each base change is the induced map of fibre products $\mathrm{pullback.map}$ along the given endomorphism of $O.G$ over the base and the identity on $\mathrm{resPt}\ Pl\ggg\Lambda.\sigma_A$, using that the endomorphism lies over $O.g$, and $O.L.\mathrm{schemeNsmul}\ p$ is the multiplication-by-$p$ endomorphism of $O.G$ attached to the relative group law $O.L$.
--
--   This is the scheme-theoretic form of the assertion, going back to Deligne–Rapoport and used by Ribet in level lowering, that on the relevant part of the special fibre of the Jacobian of the modular curve of level $\Gamma_H(M)$ at a prime $p$ exactly dividing $M$ — here the kernel of `O.abqFibre 1` — the operator $U_p$ composed with a diamond operator inverts, up to multiplication by $p$, the relative Frobenius. It is applied in [`ModularCurve.JHNeronObjectAtP.exists_units_forall_qc_comp_baseChange_U_comp_diamond_comp_eq_qc_comp_verschiebung_of_ordinaryIdempotent_of_bridge`](thm.html#ModularCurve.JHNeronObjectAtP.exists_units_forall_qc_comp_baseChange_U_comp_diamond_comp_eq_qc_comp_verschiebung_of_ordinaryIdempotent_of_bridge), where the identity is recast as the statement that $U_p$ acts as a Verschiebung on the ordinary part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul.lean

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
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.JZeroNeronObjectAtP

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.JHNeronObjectAtP.exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))
    (S : Set ℕ)

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

    (hp0 : (p : Γ((RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g), ⊤)) = 0)

    (hΦ : (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g) p 1 Fact.out hp0 ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA)) ≫ O.g =
      pullback.snd O.g (resPt Pl ≫ Λ.σA) ≫ (resPt Pl ≫ Λ.σA)) :
    ∃ d₀ : (ZMod M)ˣ,
      (pullback.fst (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 :
          Limits.pullback (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 ⟶ (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g)) ≫
        pullback.lift (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g) p 1 Fact.out hp0 ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA))
          (pullback.snd O.g (resPt Pl ≫ Λ.σA)) hΦ ≫
        (pullback.map O.g (resPt Pl ≫ Λ.σA) O.g (resPt Pl ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).2).symm) (by rw [Category.comp_id, Category.id_comp])) ≫
        (pullback.map O.g (resPt Pl ≫ Λ.σA) O.g (resPt Pl ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.dia d₀)).1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.dia d₀)).2).symm) (by rw [Category.comp_id, Category.id_comp])) =
      (pullback.fst (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 :
          Limits.pullback (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 ⟶ (RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g)) ≫
        (pullback.map O.g (resPt Pl ≫ Λ.σA) O.g (resPt Pl ≫ Λ.σA) (⟨O.L.schemeNsmul p, O.L.schemeNsmul_over p⟩ : SchemeHomOver O.g O.g).1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact ((⟨O.L.schemeNsmul p, O.L.schemeNsmul_over p⟩ : SchemeHomOver O.g O.g).2).symm) (by rw [Category.comp_id, Category.id_comp])) := by sorry
