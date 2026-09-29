-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_cuspLawInfty_prolongationDatum_offDiag_of_residue
-- name    : ModularCurve.XHDRModelAtP.cuspLawInfty_prolongationDatum_offDiag_of_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/91023fdb-4576-534d-9ce2-f5b67ef6f330
-- title:
--   ∞-side cusp law for the prolongation datum at p ∥ M
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and the hypothesis `hj` that `jqModC ℚ` lies in the $q$-expansion function field of level $\mathrm{SL}(2,\mathbb{Z})$ over $\mathbb{Q}$. Let $\mathfrak{X}$ be a model in the sense of `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ lift the structural map to $\overline{\mathbb{Q}}$. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ represented by $p$, let $\delta$ be the map on places of $\mathrm{Fbar} =$ `qExpFunctionFieldC κ (ΓN p M H hpM)` given by the semilinear action of the diamond automorphism `diamondActionModL` at the $\Gamma_0(M/p)$-lift of $pb$, and let $\theta$ be a $\overline{\mathbb{Q}}$-automorphism of $F_M =$ `xHFunctionFieldBar M H`. Assume `hwgen`: whenever two $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base satisfy that $y'$ followed by `eeta`, the first pullback projection and $\mathfrak{X}.w.\mathrm{hom}$ agrees with $y$ followed by `eeta` and the first projection, the associated places satisfy $\mathrm{pointEquivPlace}(y') = \theta \cdot \mathrm{pointEquivPlace}(y)$. Let $\alpha : F_{M/p} \to F_M$ be a $\overline{\mathbb{Q}}$-algebra map, where $F_{M/p} =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, inducing the identity on underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral. Let $Psp$ be a `JHPlaceSpecialization` for these data and $Rpd = (R_1, R_2)$ a `ProlongationDatum` for $Psp$ and $\theta$, subject to the residue compatibility `hres₂α`: for $v \in F_{M/p}$ with $\alpha v$ in both valuation rings, $R_2$-residue of $\alpha v$ is the relative Frobenius `qExpFrobeniusModL` at $p$ of its $R_1$-residue. Assume finally the two component-coordinate clauses `hcomp` and `hcompat'`: for each $i \in \{0,1\}$, each point $y$ as above, each $A$-point $u$ of the model over $\mathrm{Spec}\,\rho$ agreeing with $y$ after `eeta` and the first projection, each $\kappa$-point $u_\kappa$ of the fibre compatible with $u$ and splitting the base projection, and each closed point $P_0$ of the fibre curve model $\mathfrak{X}.\mathrm{Mfib}$ sent by `efib` followed by the $i$-th component map to the closed point of $u_\kappa$, the place of $P_0$ equals $\mathrm{reduceFst}(\alpha)(\mathrm{pointEquivPlace}\,y)$ if $i = 0$ and $\mathrm{reduceSnd}(\theta \circ \alpha, \delta)(\mathrm{pointEquivPlace}\,y)$ otherwise, while off the diagonal $\mathrm{reduceSnd}(\theta \circ \alpha, \delta)(\mathrm{pointEquivPlace}\,y) = \delta(\mathrm{qExpFrobeniusPlaceModL}$ of the place of $P_0)$ when $i = 0$, and $\mathrm{reduceFst}(\alpha)(\mathrm{pointEquivPlace}\,y) = \mathrm{qExpFrobeniusPlaceModL}$ of the place of $P_0$ when $i = 1$. The conclusion is `Rpd.CuspLawInfty α hα`: for every $f \in F_M$ lying in the valuation rings of both $R_1$ and $R_2$ with both residues non-zero, every divisor $D$ on places of $F_M$ with $D(W) = \mathrm{ord}_W(f)$ for all $W$, and every place $c$ satisfying the predicate `IsInftySide`, the push-forward along $W \mapsto Psp.\mathrm{sp}(W|_\alpha)$ of the part of $D$ supported on the `IsInftySide` places, evaluated at $Psp.\mathrm{sp}(c|_\alpha)$, equals the order of the $R_1$-residue of $f$ at that place.
--
--   This is the cusp law on the $\infty$-side cuspidal family: it states that the specialisation map $\mathrm{reduceFst}$ transports the $\infty$-part of the divisor of a function that is a unit for both prolongations to the divisor of its first residue, at $\infty$-side cusps. It is one of the clauses assembled in [`ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen), which produces the place specialisation together with its prolongation datum from the Deligne–Rapoport model of $X_H(M)$ at a prime exactly dividing $M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_cuspLawInfty_prolongationDatum_offDiag_of_residue.lean

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

theorem ModularCurve.XHDRModelAtP.cuspLawInfty_prolongationDatum_offDiag_of_residue
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
    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    Rpd.CuspLawInfty α hα := by sorry
