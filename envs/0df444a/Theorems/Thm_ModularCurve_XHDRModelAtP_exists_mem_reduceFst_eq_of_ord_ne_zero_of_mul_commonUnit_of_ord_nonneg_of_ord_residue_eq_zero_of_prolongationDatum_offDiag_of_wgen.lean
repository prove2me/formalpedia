-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/83986442-eb49-570e-95de-77dae84ca51e
-- title:
--   Non-strict zeros of a pole-free factor lie over supersingular nodes
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$; assume $j$'s $q$-expansion `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, and let $\mathfrak{X}$ be a model datum of type `XHDRModelAtP p M H hpM hj`. Let $A \subset \overline{\mathbb{Q}}$ be a valuation subring with $p$ a nonunit, with algebraically closed residue field $\kappa$ of characteristic $p$, and $\rho : R_p \to A$ lifting the structure map to $\overline{\mathbb{Q}}$. Write $F_M =$ `xHFunctionFieldBar M H`, $F_{M/p}$ for its level-$M/p$ analogue with the subgroup `infSubgroup p M H hpM`, and $\bar F =$ `Fbar p M H hpM κ`. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ with underlying residue $p$, and let $\delta$ be the action on places of $\bar F$ of the diamond automorphism `diamondActionModL` attached to a $\Gamma_0(M/p)$-lift of $pb$; let $SS$ be the finset of pairs $(\varphi y, y)$ with $y$ a supersingular place of $\bar F$ and $\varphi =$ `qExpFrobeniusPlaceModL`. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$ commuting with the arithmetic Galois action, $\alpha : F_{M/p} \to F_M$ an integral $\overline{\mathbb{Q}}$-algebra map with $\theta \circ \alpha$ integral, $\alpha$ the identity on $q$-expansions and $\theta \circ \alpha$ inducing $q \mapsto q^p$ (`qExpand`). Let $Psp$ be a place-specialisation datum `JHPlaceSpecialization p M H hpM A`, with readings $r_1(V) = Psp.\mathrm{sp}(V|_\alpha)$ and $r_2(V) = \delta(Psp.\mathrm{sp}(V|_{\theta \circ \alpha}))$, and $Rpd$ a `ProlongationDatum` for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue fields in $\bar F$, matched through $\theta$. Assumed further: the type dichotomy `TypeDichotomy`, the model laws `IsModel` (the two divisor laws and the cusp laws at $\infty$ and $0$), the order law at $\delta$-fixed affine places `OrderLawFixed`, the regularity and node-value laws for $SS$, the condition `hwgen` that whenever $y'$ followed by `𝔛.eeta`, the first pullback projection and `𝔛.w.hom` agrees with $y$ followed by `𝔛.eeta` and that projection, the place of $y'$ is $\theta$ applied to that of $y$, and two compatibility hypotheses (summarised here) identifying the place attached by the fibre curve model `𝔛.Mfib A hA ρ hρ` to a closed point over a given $\kappa$-point with $r_1$, $r_2$ and their Frobenius twists. Finally let $Hh, Kk \in F_M$ be non-zero with $Hh \cdot Kk$ lying in the integers of both $R_1$ and $R_2$ with non-zero residues there, such that $\operatorname{ord}_V Hh \ge 0$ and $\operatorname{ord}_V Kk \ge 0$ at every place $V$ of $F_M$ which is cuspidal (no $A$-integral value of $j$) or has $r_1(V)$ affine and $\delta$-fixed, and such that both residues of $Hh \cdot Kk$ have order $0$ at every place $w$ of $\bar F$ that is either non-affine or affine, $\delta$-fixed and non-supersingular. The conclusion: every place $V$ of $F_M$ with $\operatorname{ord}_V Hh \ne 0$ that is strict of neither the first nor the second kind satisfies $r_1(V) = s_1$ for some pair $s \in SS$.
--
--   This is the positivity step in the analysis of the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$: the zeros and poles of a factor of a function that is a unit on both Gauss components are confined to the supersingular gluing locus. It feeds the construction of residue carriers for vertical units in [`ModularCurve.XHDRModelAtP.exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen.lean

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

theorem ModularCurve.XHDRModelAtP.exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen
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

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (Hh Kk : ↥(xHFunctionFieldBar M H)) (hH0 : Hh ≠ 0) (hK0 : Kk ≠ 0)
    (h₁ : Hh * Kk ∈ Rpd.R₁.integers) (hr₁ : Rpd.R₁.residue ⟨Hh * Kk, h₁⟩ ≠ 0)
    (h₂ : Hh * Kk ∈ Rpd.R₂.integers) (hr₂ : Rpd.R₂.residue ⟨Hh * Kk, h₂⟩ ≠ 0)

    (hHpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V ∨ (JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V))) → 0 ≤ V.ord Hh)
    (hKpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V ∨ (JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V))) → 0 ≤ V.ord Kk)

    (hres : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A w ∨ (JHPlaceSpecialization.IsAffinePlace p M H hpM A w ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w ∧ w ∉ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)) →
      w.ord (Rpd.R₁.residue ⟨Hh * Kk, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0 ∧ w.ord (Rpd.R₂.residue ⟨Hh * Kk, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0) :
    ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord Hh ≠ 0 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V → ∃ s ∈ SS, Psp.reduceFst α hα V = s.1 := by sorry
