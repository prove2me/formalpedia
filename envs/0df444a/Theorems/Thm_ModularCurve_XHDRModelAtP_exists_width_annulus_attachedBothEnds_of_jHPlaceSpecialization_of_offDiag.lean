-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_width_annulus_attachedBothEnds_of_jHPlaceSpecialization_of_offDiag
-- name    : ModularCurve.XHDRModelAtP.exists_width_annulus_attachedBothEnds_of_jHPlaceSpecialization_of_offDiag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/d554c1e3-776b-5d10-8f59-25b04330ecc6
-- title:
--   Node annuli at supersingular crossings, attached at both ends
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial, and assume $j$ lies in the $q$-expansion function field of $SL(2,\mathbb{Z})$; let $\mathfrak{X}$ be an `XHDRModelAtP` for these data, i.e. a proper flat integral model of $X_H(M)$ over $R_p$ together with a curve model `Meta` of $\overline{\mathbb{Q}}\cdot F(X_H(M))$, an isomorphism `eeta` onto its geometric generic fibre, and the structure recorded in that definition. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ and algebraically closed residue field $\kappa$ of characteristic $p$, and $\rho : R_p \to A$ a ring map compatible with the structure map to $\overline{\mathbb{Q}}$. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ reducing to $p$, and let $\delta$ be the action on places of $\kappa \cdot F(\Gamma_N)$ induced, through `SemilinearAut.ofAlgAut`, by the diamond automorphism attached to a $\Gamma_0(M/p)$-lift of $pb$. Let $SS$ be the finset of pairs of places whose members are exactly the pairs $(\mathrm{Frob}_p(v), v)$ with $v$ supersingular, $\mathrm{Frob}_p$ being `qExpFrobeniusPlaceModL`. Let $\theta$ be a $\overline{\mathbb{Q}}$-automorphism of $F_M := \overline{\mathbb{Q}}\cdot F(X_H(M))$, $\alpha : F_{M/p} \to F_M$ an integral $\overline{\mathbb{Q}}$-algebra map acting as the identity on Laurent series, with $\theta \circ \alpha$ also integral; let $Psp$ be a `JHPlaceSpecialization` (a specialisation $\mathrm{sp}$ of places of $F_{M/p}$ to places of $\kappa\cdot F(\Gamma_N)$ together with its divisor and Picard compatibilities), and $Rpd$ a `ProlongationDatum` for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ linked by $\theta$. Assume: `hwgen`, that $\theta$ computes the action of the degeneracy map `w` on geometric points of `Meta`; the type dichotomy `hTD` for the pair $(\alpha, \theta\circ\alpha)$ and $\delta$; the model law `hmodel` for $Rpd$; and the two compatibility tables `hcompat`, `hcompat'` identifying, for each component index $i \in \{0,1\}$, the place of the special fibre model attached to a closed point lying above the reduction of a given geometric point with $Psp.\mathrm{reduceFst}\,\alpha$ or $Psp.\mathrm{reduceSnd}\,(\theta\circ\alpha)\,\delta$ of the corresponding place, respectively with their Frobenius twists. Then there is a function $e : SS \to \mathbb{N}$ with $e(s) > 0$ for all $s$, such that each $s = (s_1, s_2) \in SS$ carries an annulus $An$ of $F_M$ over $A$ (in the sense of `Annulus`: a domain of rational places, a parameter, and a modulus in the maximal ideal of $A$, with the uniqueness, order and unit axioms) satisfying: a place $W$ of $F_M$ lies in $An.\mathrm{dom}$ exactly when $Psp.\mathrm{reduceFst}\,\alpha\,W = s_1$ and $W$ is neither `IsStrictFst` nor `IsStrictSnd`; $An.\mathrm{modulus} = p^{e(s)}u$ for some unit $u$ of $A$; the parameter $An.\mathrm{param}$ is fixed by the arithmetic Galois action of every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$; $An.\mathrm{modulus}^{-1}\cdot An.\mathrm{param}$ lies in the valuation ring of $R_1$, while $An.\mathrm{param}$ lies in that of $R_2$ with non-zero $R_2$-residue; moreover $\mathrm{ord}_{s_2}$ of the $R_2$-residue of $An.\mathrm{param}$ equals $1$ and, for every $f$ in the valuation ring of $R_2$ with non-zero residue and with $\mathrm{ord}_P f = 0$ for all $P \in An.\mathrm{dom}$, the value $f(P)\cdot An.\mathrm{param}(P)^{-\mathrm{ord}_{s_2}(\bar f)}$ lies in $A$ and is a unit there for every $P \in An.\mathrm{dom}$; and the mirror statement at the other end, with $An.\mathrm{modulus}\cdot An.\mathrm{param}^{-1}$ in the valuation ring of $R_1$, its $R_1$-residue of $\mathrm{ord}_{s_1}$ equal to $1$, and the same unit law for $R_1$, $s_1$ and this flipped parameter.
--
--   This is the annulus statement for the supersingular crossings of the Deligne–Rapoport model of $X_H(M)$ at a prime exactly dividing the level: each node of the special fibre contributes a $p$-adic annulus of width $e(s)$ in the geometric generic fibre, with inertia-invariant parameter, and the annulus is attached at its two ends to the two Gauss prolongations $R_1$, $R_2$, the end-slope laws recording the orders of residues at the two places of the node. It is used by the construction of the specialisation and component-group package for the Jacobian at $p$ and by the extension-of-points statement that feeds the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_width_annulus_attachedBothEnds_of_jHPlaceSpecialization_of_offDiag.lean

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

theorem ModularCurve.XHDRModelAtP.exists_width_annulus_attachedBothEnds_of_jHPlaceSpecialization_of_offDiag
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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    ∃ (e : ↥SS → ℕ), (∀ s, 0 < e s) ∧
    ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) := by sorry
