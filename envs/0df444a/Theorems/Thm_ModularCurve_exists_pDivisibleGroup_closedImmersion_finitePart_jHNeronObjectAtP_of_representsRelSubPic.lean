-- Prove2me | Theorems.Thm_ModularCurve_exists_pDivisibleGroup_closedImmersion_finitePart_jHNeronObjectAtP_of_representsRelSubPic
-- name    : ModularCurve.exists_pDivisibleGroup_closedImmersion_finitePart_jHNeronObjectAtP_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/4cebeefb-8bb6-5ec4-9d72-e5a803210d64
-- title:
--   A p-divisible group inside the Néron object of J_H(M)
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit congruent to $1$ modulo $M/p$ (with $M/p$ nonzero), and a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ with $p$ in its nonunits whose residue field is algebraically closed of characteristic $p$; assume the $q$-expansion `jqModC` of $j$ lies in the level-$\top$ $q$-expansion function field. Given a Deligne–Rapoport model $\mathfrak{X}$ of `XHDRModelAtP p M H`, level data $\Lambda$, a Néron object $O$ for $J_H(M)$ at $p$ over $Pl$, and witnesses that the relative $\mathrm{Pic}^0$ functors for the fibrewise-algebraically-trivial condition at levels $\Gamma_M$ and $\Gamma_N$ are represented by the designations built from $(O.G,O.g)$ and from $(\Lambda.X,\Lambda.f)$ with their unit sections, together with a henselian local domain $R_h$ mapping faithfully into $\overline{\mathbb{Q}}$ with image inside $Pl$ and with maximal ideal consisting exactly of the elements of $Pl$-valuation $<1$, the conclusion asserts the existence of a height $h$, a $p$-divisible group $\mathcal{G}$ over $R_h$ of height $h$ (finite free cocommutative Hopf algebras $\mathcal{G}.level\,v$ of rank $p^{vh}$ with surjective transitions), a ring map $\rho_h\colon \mathbb{Z}_{(p)} \to R_h$ compatible with the two embeddings into $\overline{\mathbb{Q}}$, and morphisms $\iota_v\colon \operatorname{Spec}(\mathcal{G}.level\,v) \to O.G$ such that: each $\iota_v$ lies over $\operatorname{Spec}\rho_h$ via the structure map of $\mathcal{G}.level\,v$; the resulting morphism to the pullback of $O.g$ along $\operatorname{Spec}\rho_h$ is a closed immersion; $\iota_v$ is killed by the multiplication-by-$p^v$ map of the group law $O.L$; for every $R_h$-algebra $B$ and points $x,y$ of $\mathcal{G}$ at level $v$ over $B$ lying over the base, the point attached to $x\cdot y$ is the $O.L$-product of those attached to $x$ and $y$; the $\iota_v$ are compatible with the transition maps; for every set $S$ of naturals and every Hecke generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) there is a family of bialgebra endomorphisms $\varphi_v$ of $\mathcal{G}.level\,v$ commuting with the transitions and with $\iota_v$ intertwining $\varphi_v$ and $O.\mathrm{hecke}\,S\,g$; the induced morphism $j_v$ from $\operatorname{Spec}(\mathcal{G}.level\,v)$ to the base change to $R_h$ of the $p^v$-kernel of $O.L$ is both an open and a closed immersion whose image contains every point lying over the closed point of $R_h$; and finally $\#\mathrm{Pic}^0(\overline{\mathbb{Q}}, \overline{F}_H)[p^v] = p^{v(h + O.\mathrm{toricRank})}$ for all $v$.
--
--   This is the construction of the finite part of the $p$-power torsion of the Néron object of $J_H(M)$ at a prime $p$ exactly dividing $M$, in the form of a $p$-divisible group over a henselian local base, realised inside the kernel schemes as an open and closed subscheme containing the special fibre, equivariant for the Hecke symbols, with its height pinned down by the $p$-power torsion count of $\mathrm{Pic}^0$ and the toric rank. It is the scheme-theoretic input to the subsequent analysis of the Raynaud extension and of the toric part of the Néron object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pDivisibleGroup_closedImmersion_finitePart_jHNeronObjectAtP_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.exists_pDivisibleGroup_closedImmersion_finitePart_jHNeronObjectAtP_of_representsRelSubPic
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    :
    ∃ (h : ℕ) (𝒢 : PDivisibleGroup Rh p h) (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
      (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G),
      (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ) ∧
      (∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)) ∧
      (∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1)) ∧
      (∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ∧
      (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v) ∧
      (∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
        (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
        (∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1)) ∧
      (∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base) ∧

      (∀ v : ℕ, Nat.card ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v)) = p ^ (v * (h + O.toricRank))) := by sorry
