-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow
-- name    : ModularCurve.XHDRModelAtP.exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/f1580662-0356-5df2-815d-0bb621899ac1
-- title:
--   Splitting of π⁻¹[u] over the geometric generic fibre
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbf{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbf{Z}/(M/p))^\times$, and the hypothesis $hj$ that $jqModC\ \mathbf{Q}$ lies in the $q$-expansion function field of $SL(2,\mathbf{Z})$; let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, i.e. a bundle of integral models of $X_H(M)$ and $X_{H,0}(p)$-type level over $R\,p$ together with the curve model `Meta` of the geometric generic fibre, the degeneracy morphism $\pi$ with $\pi \cdot$ `toBase` $=$ `toBase`, and the fibrewise dictionary data; the structure maps `toBase` at both levels are assumed separated. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and $\rho : R\,p \to A$ a ring homomorphism inducing the structural map $R\,p \to \overline{\mathbf{Q}}$. Given a $\overline{\mathbf{Q}}$-point $y$ of $\mathfrak{X}$`.Meta.C`, a section $u$ of `toBase p (ΓM M H) hj` over $\operatorname{Spec}\rho$ whose restriction along $A \subseteq \overline{\mathbf{Q}}$ is $y$ transported through $\mathfrak{X}$`.eeta` and the first projection, with image contained in $\mathfrak{X}$`.smoothLocus`, a section $u_\kappa$ of the fibre over the residue field reducing $u$, and a closed point $P$ of $\mathfrak{X}$`.Mfib A hA ρ hρ`$.C$ whose image under $\mathfrak{X}$`.efib` followed by the zeroth component map is the closed point of $u_\kappa$ and whose place differs from $\mathfrak{X}$`.placeOn0 A hA ρ hρ n` for every $n$ in the pullback of the two component maps, the conclusion asserts: there are $k$, sections $u'_j$ ($j \in$ `Fin k`) of `toBase p (ΓM M H) hj` over $\operatorname{Spec}\rho$ and positive integers $e_j$ with $\sum_j e_j = p$, such that each $u'_j$ restricted along $A \subseteq \overline{\mathbf{Q}}$ comes from a $\overline{\mathbf{Q}}$-point $y'_j \ne y$, satisfies $u'_j$ followed by $\pi$ equals $u$ followed by $\pi$, has image in $\mathfrak{X}$`.smoothLocus`, and admits a reduction $u'_{\kappa,j}$ over the residue field together with a closed point $P'_j$ lying on the first component above $u'_{\kappa,j}$ with `qExpFrobeniusPlaceModL` of the place of $P'_j$ equal to the place of $P$; moreover the finrank of $\pi$ at the image of the closed point of $\overline{\mathbf{Q}}$ under $u$ followed by $\pi$ is $p + 1$; and the ideal sheaf of the relative effective Cartier divisor of the point $u$ followed by $\pi$, pulled back along `curveChange` for $\pi$ and then along `mapOnProdOver` for $A \subseteq \overline{\mathbf{Q}}$, equals the product of the ideal sheaf of the divisor of $u$ with $\prod_j$ (ideal sheaf of the divisor of $u'_j$)$^{e_j}$, pulled back along the same `mapOnProdOver`.
--
--   This is the geometric generic-fibre half of the computation of the pull-back divisor $\pi^{*}[\pi \circ u]$ for the degeneracy morphism $\pi$ between the Deligne–Rapoport-style integral models at a prime exactly dividing the level: the fibre of $\pi$ through $u$ has degree $p + 1$, and apart from $u$ itself it consists of sections whose reductions lie on the other component and are Frobenius-related to the place of $P$. It is used by [`ModularCurve.XHDRModelAtP.exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le`](thm.html#ModularCurve.XHDRModelAtP.exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP₀ : ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ 𝔛.placeOn0 A hA ρ hρ n) :
    ∃ (k : ℕ) (u' : Fin k → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)) (e : Fin k → ℕ),
      (∀ j, 0 < e j) ∧ ∑ j, e j = p ∧
      (∀ j, ∃ y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
        Spec.map (CommRingCat.ofHom A.subtype) ≫ (u' j).1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧ y' ≠ y) ∧
      (∀ j, (u' j).1 ≫ 𝔛.π.1 = u.1 ≫ 𝔛.π.1) ∧
      (∀ j, Set.range (u' j).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) ∧
      (∀ j, ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (u' j).1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P') =
            (𝔛.Mfib A hA ρ hρ).placeOfPoint P) ∧

      𝔛.π.1.finrank ((Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 ≫ 𝔛.π.1).base
        (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) = p + 1 ∧

      ((RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (u.1 ≫ 𝔛.π.1)
          ((Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) 𝔛.π.2).trans u.2))).I.comap
          (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ)))).comap
          (mapOnProdOver (toBase p (ΓM M H) hj)
            (g' := Spec.map (CommRingCat.ofHom ρ)) (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
            (Spec.map (CommRingCat.ofHom A.subtype)) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) =
        ((RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u.1 u.2).I *
          ∏ j, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (u' j).1 (u' j).2).I ^ (e j)).comap
          (mapOnProdOver (toBase p (ΓM M H) hj)
            (g' := Spec.map (CommRingCat.ofHom ρ)) (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
            (Spec.map (CommRingCat.ofHom A.subtype)) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) := by sorry
