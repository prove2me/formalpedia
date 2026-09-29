-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp
-- name    : ModularCurve.XHDRModelAtP.isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/6e7bb972-da73-56be-bb02-50d4e42273be
-- title:
--   Cuspidal generic place iff non-affine special point
-- statement:
--   Fix a prime $p$ and $M$ with $M \neq 0$, $p \mid M$, $p^2 \nmid M$ and $M/p \neq 0$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$; assume the $q$-expansion `jqModC ℚ` of $j$ lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the level-one integral form ratios. Let $\mathfrak{X}$ be a datum of type `XHDRModelAtP p M H hpM hj`: it bundles properness, flatness, integrality and local finite presentation of the two-chart $j$-line model `toBase p (ΓM M H) hj` over `R p`, integral closedness of its affine sections, properness and relative smoothness of dimension one of the level-`ΓN p M H hpM` model, a curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` identified by the isomorphism `𝔛.eeta` with the generic fibre of that model, and further compatibility data, summarised here. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ in which $p$ is a nonunit, with algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho \colon$ `R p` $\to A$ satisfy $A.\mathrm{subtype} \circ \rho =$ `algebraMap (R p) (AlgebraicClosure ℚ)`. Let $i \in \{0,1\}$, let $y$ be a $\overline{\mathbb{Q}}$-point of `𝔛.Meta.C` splitting `𝔛.Meta.toBase`, let $u \colon \operatorname{Spec} A \to$ `X p (ΓM M H) hj` be a morphism whose composite with the structure map is $\operatorname{Spec} \rho$, and assume that restricting $u$ along $A \hookrightarrow \overline{\mathbb{Q}}$ gives $y$ read in the model through `𝔛.eeta` followed by the first projection. Let $u_\kappa$ be a morphism from $\operatorname{Spec} \kappa$ to `fibre ((IsLocalRing.residue ↥A).comp ρ)` whose second projection is the identity and whose first projection is the reduction of $u$ along $A \to \kappa$. Finally let $P_0$ be a closed point of the curve model `𝔛.Mfib A hA ρ hρ` whose image under `𝔛.efib A hA ρ hρ` followed by the $i$-th component map `𝔛.comp A hA ρ hρ i` is the image of the closed point of $\operatorname{Spec} \kappa$ under $u_\kappa$. The assertion is an equivalence: the place `𝔛.Meta.pointEquivPlace y` of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ is cuspidal, that is, for every element $x$ of that function field whose Laurent expansion equals `jqModC (AlgebraicClosure ℚ)` and every $a \in A$ the order of $x - a$ at the place is $\le 0$, if and only if the place `(𝔛.Mfib A hA ρ hρ).placeOfPoint P0` of `JHNeronObjectAtP.Fbar p M H hpM κ` is not affine, that is, there are no element $x$ of that field with Laurent expansion `jqModC κ` and no $a \in \kappa$ with $x$ in the valuation ring of the place and residue $a$.
--
--   This identifies, for an $A$-valued section of the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$, the condition that $j$ takes no $A$-integral value at the generic place with the condition that $\bar{j}$ has a pole at the specialisation of the section on the chosen component of the special fibre. It is used in the analysis of the two components of the special fibre, in particular by [`ModularCurve.XHDRModelAtP.isZeroSide_iff_isInftySide_smul_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.isZeroSide_iff_isInftySide_smul_prolongationDatum) and by the existence result for the $\infty$-side and $0$-side readings of a non-affine place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.isCuspidal_iff_not_isAffinePlace_placeOfPoint_of_section_comp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (i : Fin 2)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace y) ↔ ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0) := by sorry
