-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOn_germ_eq_zero_of_isUnit_section
-- name    : ModularCurve.XHDRModelAtP.ord_placeOn_germ_eq_zero_of_isUnit_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/c08d471d-8705-58e6-87ed-81250231f8a4
-- title:
--   Unit sections have order zero at both places of a node
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, the hypotheses $p^2 \nmid M$ and that every $u \in (\mathbb{Z}/M)^\times$ mapping to $1$ in $(\mathbb{Z}/(M/p))^\times$ lies in $H$, and the hypothesis `hj` that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field of level $\mathrm{SL}_2(\mathbb{Z})$. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be a ring map compatible with $R_p \to \overline{\mathbb{Q}}$. Let $n$ be a point of the fibre product of the two component maps $\mathfrak{X}.\mathrm{comp}\,0$ and $\mathfrak{X}.\mathrm{comp}\,1$, let $U'$ be an open of the base change `XO (ΓM M H) hj ρ`, assume the image of $n$ under `pullback.fst` followed by $\mathfrak{X}.\mathrm{comp}\,0$ followed by the comparison map `bcMap` lies in $U'$, and let $\gamma \in \Gamma(\mathrm{XO}, U')$ be a unit. Then, for each of $i = 1$ and $i = 0$, the generic point of the curve $\mathfrak{X}.\mathrm{Mfib}$ lies in the preimage of $U'$ under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\,i$ followed by `bcMap`, and the germ there of the pulled-back section $\gamma$, read through the isomorphism `ffEquiv` of the curve model with its function field, is nonzero and has $\mathrm{ord}$ equal to $0$ at the place $\mathfrak{X}.\mathrm{placeOn1}\,n$ (respectively $\mathfrak{X}.\mathrm{placeOn0}\,n$), these being the place of the $q$-expansion function field at level `ΓN p M H hpM` attached to $n$ by $\mathfrak{X}.\mathrm{nodeEquiv}$ and its restriction along the mod-$p$ Frobenius.
--
--   This records that a section which is invertible on a neighbourhood of a crossing point of the special fibre of the Deligne–Rapoport model restricts, on each of the two branches through that crossing, to a nonzero function of order zero at the corresponding place. It feeds the construction that a function with unit values near a node has a unit germ there, used in the comparison of the two components of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_ord_placeOn_germ_eq_zero_of_isUnit_section.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP MvPolynomial
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.ord_placeOn_germ_eq_zero_of_isUnit_section
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (U' : (XO (ΓM M H) hj ρ).Opens)
    (hx : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫
      bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base n ∈ U')
    (γ : Γ(XO (ΓM M H) hj ρ, U')) (hγ : IsUnit γ) :
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
     ∃ hg1 : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ U',
      (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ U') (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg1)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA).app U').hom γ)) ≠ 0 ∧
      (𝔛.placeOn1 A hA ρ hρ n).ord
        ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ U') (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg1)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA).app U').hom γ))) = 0) ∧
    (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
     ∃ hg0 : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ U',
      (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ U') (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg0)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).app U').hom γ)) ≠ 0 ∧
      (𝔛.placeOn0 A hA ρ hρ n).ord
        ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ U') (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg0)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).app U').hom γ))) = 0) := by sorry
