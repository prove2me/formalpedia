-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_placeOfPoint_frobeniusTwist_eq_smul
-- name    : ModularCurve.XHDRModelAtP.exists_placeOfPoint_frobeniusTwist_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/a857325a-890c-5614-81d2-c1bcc8abcd0b
-- title:
--   Relative Frobenius twists places of closed fibre points
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ and $M/p$ nonzero, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis $hj$ that the $q$-series `jqModC` over $\mathbb{Q}$ lies in `qExpFunctionFieldC ℚ ⊤`, the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios for the full group $SL(2,\mathbb{Z})$. Let $\mathfrak{X}$ be an element of the structure `XHDRModelAtP p M H hpM hj`, i.e. a package of integral-model data over $R\,p$ for the curves of level $\Gamma_M$ and $\Gamma_N$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : R\,p \to A$ be a ring map compatible with the structure map $R\,p \to \overline{\mathbb{Q}}$. Let $\mathrm{frob}$ be a semilinear automorphism of $F' :=$ `qExpFunctionFieldC` of the residue field $\kappa$ at level $\Gamma_N\,p\,M\,H$ over $\kappa$, that is, a pair consisting of a ring automorphism of $F'$ and one of $\kappa$ intertwined by the structure map, and assume $\mathrm{frob}$ raises every Laurent coefficient, in every degree $n \in \mathbb{Z}$, to the $p$-th power. Let the fibre $\mathfrak{X}_{0,\kappa} :=$ `fibre` be the pullback of the level-$\Gamma_N$ structure map `toBase` along $\operatorname{Spec}$ of $\mathrm{residue} \circ \rho$, assume $p = 0$ in its global sections, and let $\theta_N$ be an endomorphism of this fibre whose composition with the first projection agrees with that of the absolute Frobenius `frobenius p 1` on the model factor, and whose composition with the second projection is the second projection. Then for every closed point $P$ of the curve model $\mathfrak{X}.\mathrm{Mfib}$ over $\kappa$ with function field $F'$, the image of $P$ under the underlying map of $\mathfrak{X}.\mathrm{efib}$ followed by $\theta_N$, pulled back along the inverse of $\mathfrak{X}.\mathrm{efib}$, is again a closed point, and its place in the sense of `placeOfPoint` equals $\mathrm{frob}$ applied to the place of $P$.
--
--   This is the statement that on the characteristic-$p$ fibre of the Deligne–Rapoport model the relative Frobenius acts on the places of the function field $F'$ of that fibre by the coefficientwise $p$-th power map on $q$-expansions, i.e. it identifies the geometric Frobenius of the fibre with the arithmetic Frobenius of $F'/\kappa$. It is used in the analysis of the reduction of points of the Néron model attached to $J_H$ at $p$, via [`ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction`](thm.html#ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction), on the way to the Eichler–Shimura congruence relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_placeOfPoint_frobeniusTwist_eq_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_placeOfPoint_frobeniusTwist_eq_smul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (frob : SemilinearAut (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)))
    (hfrob : ∀ (x : ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM))) (n : ℤ),
      ((frob • x : ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM))) :
          LaurentSeries (ResidueField ↥A)).coeff n =
        ((x : LaurentSeries (ResidueField ↥A)).coeff n) ^ p)

    (hN : (p : Γ((fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), ⊤)) = 0)
    (θN : (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶ (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hθN₁ : θN ≫ pullback.fst _ _ = (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).frobenius p 1 Fact.out hN ≫ pullback.fst _ _)
    (hθN₂ : θN ≫ pullback.snd _ _ = pullback.snd _ _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C) :
    ∃ h : (inv (𝔛.efib A hA ρ hρ)).base ((𝔛.efib A hA ρ hρ ≫ θN).base P.1) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
      (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ = frob • (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by sorry
