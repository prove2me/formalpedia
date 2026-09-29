-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le
-- name    : ModularCurve.XHDRModelAtP.exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/6bbeb142-c69f-5a88-8c34-663fc852f14e
-- title:
--   Splitting along π of a section divisor on the Γ_H(M) model
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ and $p^{2} \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$ containing the kernel of the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$, and a witness `hj` that $jqModC\ \mathbb{Q}$ lies in the level-$\mathrm{SL}_2(\mathbb{Z})$ $q$-expansion function field. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`: this packages the two-chart integral models `X p (ΓM M H) hj` (proper, flat, integral, normal) and `X p (ΓN p M H hpM) hj` (proper, smooth of relative dimension $1$) over `Spec (R p)`, the morphism `𝔛.π` between them over the base, a curve model `𝔛.Meta` of the geometric function field `xHFunctionFieldBar M H` together with the isomorphism `𝔛.eeta` onto the geometric generic fibre, and special-fibre data (`𝔛.Mfib`, `𝔛.efib`, `𝔛.comp`, `𝔛.placeOn0`, `𝔛.smoothLocus`). Let $A \subseteq \overline{\mathbb{Q}}$ be a valuation subring with $p$ a non-unit of $A$ and residue field $\kappa$ algebraically closed of characteristic $p$, and $\rho : R p \to A$ a ring map whose composite with the inclusion of $A$ is the structure map $R p \to \overline{\mathbb{Q}}$; both structure maps to `Spec (R p)` are assumed separated. The data given are: a $\overline{\mathbb{Q}}$-point $y$ of `𝔛.Meta.C` (a section of `𝔛.Meta.toBase`); an $A$-valued section $u$ of `toBase p (ΓM M H) hj` along `Spec.map ρ` whose restriction to $\overline{\mathbb{Q}}$ is the point of the generic fibre determined by $y$ via `𝔛.eeta`, and whose topological image lies in `𝔛.smoothLocus`; a $\kappa$-point $u\kappa$ of the fibre `fibre ((residue A).comp ρ)` splitting the second projection and whose first projection is the reduction of $u$; and a closed point $P$ of `(𝔛.Mfib A hA ρ hρ).C` such that `𝔛.efib ≫ 𝔛.comp … 0` sends $P$ to the image of the closed point of $\kappa$ under $u\kappa$, and such that the place `placeOfPoint P` differs from `𝔛.placeOn0 A hA ρ hρ n` for every $n$ in the fibre product of `𝔛.comp … 0` and `𝔛.comp … 1`. The conclusion asserts the existence of $k \in \mathbb{N}$, sections $u'_1,\dots,u'_k$ of `toBase p (ΓM M H) hj` along `Spec.map ρ`, and multiplicities $e_1,\dots,e_k \in \mathbb{N}$ with all $e_j > 0$ and $\sum_j e_j = p$, such that: each $u'_j$ restricts over $\overline{\mathbb{Q}}$ to the generic point determined by some $y'_j \neq y$; each satisfies $u'_j$ followed by `𝔛.π.1` equals $u$ followed by `𝔛.π.1`; each has image in `𝔛.smoothLocus`; each admits a $\kappa$-point $u\kappa'_j$ of the same fibre, splitting the second projection and with first projection the reduction of $u'_j$, together with a closed point $P'_j$ of `(𝔛.Mfib A hA ρ hρ).C` carried by `𝔛.efib ≫ 𝔛.comp … 1` to the image of the closed point of $\kappa$ under $u\kappa'_j$ and with `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p (placeOfPoint P'_j) = placeOfPoint P`, i.e. the place of $P'_j$ restricted along the $p$-power endomorphism of the $q$-expansion function field is the place of $P$; and, finally, the ideal sheaf of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` of the section $u$ followed by `𝔛.π.1` (the kernel ideal sheaf of its graph in the base change of the $\Gamma_N$-level model to `Spec.map ρ`), pulled back along `curveChange 𝔛.π.1 𝔛.π.2 (Spec.map ρ)`, equals the ideal sheaf of the graph of $u$ times $\prod_j$ (ideal sheaf of the graph of $u'_j)^{e_j}$.
--
--   This is the Deligne–Rapoport description, on the model of $X_H(M)$ at $p$ over a valuation ring $A$ above $p$, of the divisor-theoretic fibre of the degeneracy morphism $\pi$ over a section meeting the component indexed $0$ away from the crossing points: the pull-back of the degree-one section divisor splits as the given section plus a divisor of total degree $p$ supported on sections whose reductions lie on the other component and are Frobenius preimages of the reduction of $u$. It is used in [`ModularCurve.XHDRModelAtP.toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq`](thm.html#ModularCurve.XHDRModelAtP.toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq), where the induced map on relative degree-zero Picard groups is computed, and rests on the computation that $\pi$ is finite flat of degree $p+1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le.lean

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

theorem ModularCurve.XHDRModelAtP.exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le
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

      (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (u.1 ≫ 𝔛.π.1)
          ((Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) 𝔛.π.2).trans u.2))).I.comap
          (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ))) =
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u.1 u.2).I *
          ∏ j, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (u' j).1 (u' j).2).I ^ (e j) := by sorry
