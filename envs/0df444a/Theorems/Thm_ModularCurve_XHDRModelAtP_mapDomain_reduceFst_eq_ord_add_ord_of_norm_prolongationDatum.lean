-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_mapDomain_reduceFst_eq_ord_add_ord_of_norm_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.mapDomain_reduceFst_eq_ord_add_ord_of_norm_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/9d51d560-ef13-549d-a590-a678892d7651
-- title:
--   Norm identity for the first reduction map at level Γ_H
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$; assume `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` structure, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ in which $p$ is a nonunit, with residue field $\kappa$ algebraically closed of characteristic $p$, and let $\rho : R\,p \to A$ be a ring map whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Write $F_M =$ `xHFunctionFieldBar M H`, $F' =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` and $\bar F =$ `Fbar p M H hpM κ`. Further data: a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$; the map $\delta$ on places of $\bar F$ given by the semilinear action of the diamond automorphism `diamondActionModL` attached to a lift of $pb$ to $\Gamma_0(M/p)$; a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$ which on places of $F_M$ induces the effect of $\mathfrak{X}.w$ on $\overline{\mathbb{Q}}$-points of $\mathfrak{X}.\mathrm{Meta}.C$ (hypothesis `hwgen`); a $\overline{\mathbb{Q}}$-algebra map $\alpha : F' \to F_M$ which is the identity on underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral; a place specialization `Psp` of type `JHPlaceSpecialization p M H hpM A`, with specialization map $\mathrm{sp}$ from places of $F'$ to places of $\bar F$; and a prolongation datum `Rpd` for `Psp` and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue field $\bar F$. Two further hypotheses are assumed: a compatibility `hcomp` identifying, for each $i \in \{0,1\}$, the place attached by the fibre model $\mathfrak{X}.\mathrm{Mfib}$ to a closed point over a given $\kappa$-point with `Psp.reduceFst α hα` respectively `Psp.reduceSnd (θ ∘ α) hβ δ` applied to the place of the corresponding $\overline{\mathbb{Q}}$-point; and the norm hypothesis `hN`: for every $f \in F_M$ integral for $R_1$ and for $R_2$ with both residues non-zero, there is a non-zero $g \in \bar F$ such that every divisor $D$ on $F'$ with $D(V) = \operatorname{ord}_V(N(f))$ for all $V$, the norm being taken for the algebra structure on $F_M$ over $F'$ along $\alpha$, satisfies $(\mathrm{sp}_* D)(v') = \operatorname{ord}_{v'}(g)$ for all places $v'$ of $\bar F$, and such that $\operatorname{ord}_{\varphi u}(g) = \operatorname{ord}_{\varphi u}(R_1.\mathrm{residue}\,f) + \operatorname{ord}_u(R_2.\mathrm{residue}\,f)$ for every place $u$ of $\bar F$, where $\varphi =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`. The conclusion: for every $f \in F_M$ integral for $R_1$ and $R_2$ with non-zero residues, every divisor $D$ on $F_M$ with $D(W) = \operatorname{ord}_W(f)$ for all places $W$, and every place $u$ of $\bar F$, the push-forward of $D$ along $W \mapsto \mathrm{sp}(W|_\alpha)$ satisfies $(\,(\mathrm{reduceFst})_* D)(\varphi u) = \operatorname{ord}_{\varphi u}(R_1.\mathrm{residue}\,f) + \operatorname{ord}_u(R_2.\mathrm{residue}\,f)$; equivalently, the sum of $\operatorname{ord}_W(f)$ over the places $W$ of $F_M$ with $\mathrm{sp}(W|_\alpha) = \varphi(u)$ equals that sum of two residue orders.
--
--   This is the norm identity of the Deuring reduction argument at level $\Gamma_H$: it transfers the order-counting hypothesis `hN`, stated for the norm of $f$ down to the function field of level $M/p$, into a statement about the fibres of the first reduction map on places of $F_M$. It is used in the verification of the cusp laws for the prolongation datum, namely in `cuspLawInfty_prolongationDatum_offDiag_of_residue` and `cuspLawZero_prolongationDatum_offDiag`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_mapDomain_reduceFst_eq_ord_add_ord_of_norm_prolongationDatum.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open AlgebraicCurve

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.mapDomain_reduceFst_eq_ord_add_ord_of_norm_prolongationDatum
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
    (hN : ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
        letI := algebraAlong α
        ∃ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), g ≠ 0 ∧
          (∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
            (∀ V, D V = V.ord (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f)) →
            ∀ v', Finsupp.mapDomain Psp.sp D v' = v'.ord g) ∧
          ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord g =
              (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord (Rpd.R₁.residue ⟨f, h₁⟩) +
                u.ord (Rpd.R₂.residue ⟨f, h₂⟩)) :
    ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, D W = W.ord f) →
        ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
          Finsupp.mapDomain (Psp.reduceFst α hα) D ((qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) u) =
            ((qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) u).ord (Rpd.R₁.residue ⟨f, h₁⟩) + u.ord (Rpd.R₂.residue ⟨f, h₂⟩) := by sorry
