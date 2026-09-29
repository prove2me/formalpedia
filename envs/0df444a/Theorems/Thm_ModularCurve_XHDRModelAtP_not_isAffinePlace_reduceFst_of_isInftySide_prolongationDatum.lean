-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/522fff49-e7fb-5a5e-956f-1e3c7028b8b0
-- title:
--   ∞-side places reduce to non-affine places under the first reading
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit that becomes $1$ in $(\mathbb Z/(M/p))^\times$, with $M/p$ nonzero, and assume the $j$ $q$-expansion `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak X$ be a model datum of type `XHDRModelAtP p M H hpM hj` (a proper flat integral $R_p$-model of the curve of level $\Gamma_M(H)$, together with a curve model `𝔛.Meta` of $F_M =$ `xHFunctionFieldBar M H` over $\overline{\mathbb Q}$, its identification `𝔛.eeta` with the geometric generic fibre, and the fibrewise data). Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and $\rho \colon R_p \to A$ a ring map whose composite with the inclusion of $A$ is the structure map $R_p \to \overline{\mathbb Q}$. Let $pb$ be a unit of $\mathbb Z/(M/p)$ whose underlying element is $p$, and let $\delta$ act on places of $\bar F' =$ `JHNeronObjectAtP.Fbar p M H hpM κ` over $\kappa$ by the semilinear automorphism attached to the diamond automorphism `diamondActionModL` for $(M/p,\$`infSubgroup p M H hpM`$)$ at a $\Gamma_0(M/p)$-lift of $pb$. Let $\theta$ be a $\overline{\mathbb Q}$-algebra automorphism of $F_M$ which realises the involution `𝔛.w` on places, in the sense that whenever two $\overline{\mathbb Q}$-points $y,y'$ of `𝔛.Meta.C` over the base satisfy: $y'$ followed by `𝔛.eeta`, the first projection and `𝔛.w.hom` equals $y$ followed by `𝔛.eeta` and the first projection, the associated places satisfy `𝔛.Meta.pointEquivPlace y'` $=$ `SemilinearAut.ofAlgAut θ` $\cdot$ `𝔛.Meta.pointEquivPlace y`. Let $\alpha \colon F_{M/p} \to F_M$ be a $\overline{\mathbb Q}$-algebra map compatible with the inclusions of both fields into Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral. Let `Psp` be a place-specialisation datum for $(p,M,H,A)$, with specialisation map $\mathrm{sp}$ from places of $F_{M/p}$ over $\overline{\mathbb Q}$ to places of $\bar F'$ over $\kappa$, and `Rpd` a prolongation datum for `Psp` and $\theta$ (two regular prolongations of $A$ to $F_M$ with residues in $\bar F'$, matched through $\theta$). Assume the component compatibility clause: for $i \in \{0,1\}$, each geometric point $y$ of `𝔛.Meta.C`, each lift of it over `Spec ρ`, each compatible section of the fibre over $\kappa$, and each closed point $P_0$ of the fibre curve model `𝔛.Mfib` whose image under `𝔛.efib` followed by the $i$-th component map is the closed point of that section, the place of $P_0$ equals $\mathrm{sp}$ of the restriction of `𝔛.Meta.pointEquivPlace y` along $\alpha$ when $i = 0$, and $\delta$ applied to $\mathrm{sp}$ of its restriction along $\theta \circ \alpha$ otherwise. Finally let $c$ be a place of $F_M$ over $\overline{\mathbb Q}$ lying on the $\infty$-side: $c$ satisfies `IsCuspidal`, and there are $x, x' \in F_M$ with $q$-expansions `jqModC` and `qExpand p jqModC` and some $\tau \in A$ of residue $1$ such that $c$ takes the value $\tau$ at $x'/x^p$. The conclusion is that the first reading $\mathrm{sp}(c|_\alpha)$ of $c$ is not an affine place: there is no element of $\bar F'$ with $q$-expansion `jqModC κ` at which this place takes a value in $\kappa$.
--
--   In the Deligne–Rapoport description of the reduction of $X_H(M)$ at $p$ with $p \parallel M$, the special fibre is a union of two copies of the curve of level $M/p$ crossing at the supersingular points, and the $\infty$-side cuspidal places of the geometric generic fibre reduce to cusps of the first component, where the reduced modular invariant $\bar j$ has a pole. This is a side lemma of the place-specialisation package, used in establishing the cusp laws on the $\infty$-branch and the étaleness and local semicontinuity statements at the $\infty$-cusp charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum.lean

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

theorem ModularCurve.XHDRModelAtP.not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
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

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : (∀ (i : Fin 2)
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
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))
    (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hc : (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) c) :
    ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) ((Psp.reduceFst α hα) c) := by sorry
