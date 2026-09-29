-- Prove2me | Theorems.Thm_ModularCurve_exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective
-- name    : ModularCurve.exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/1909c754-f95f-50f0-b8ba-c909305e06eb
-- title:
--   Residual surjectivity of K in the Gauss ring over A
-- statement:
--   Let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be a subgroup containing $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, let $k_0$ be an intermediate field of $\mathbb Q$ in $\overline{\mathbb Q}$ and $K_1$ an intermediate field of $k_0$ in $\overline{\mathbb Q}$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ and $A_1$ a valuation subring of $K_1$ whose elements are exactly those $x\in K_1$ with $x\in A$, and assume that $a\mapsto \mathrm{residue}(a)$ sends $A_1$ onto the residue field of $A$. Let $K$ be the intermediate field of $K_1$ in $K_1(\!(q)\!)$ obtained by adjoining to $K_1$ the coefficientwise images under $\mathbb Q\to K_1$ of the elements of $\mathbb Q\cdot F(\Gamma)$, where $F(\Gamma)\subseteq\mathbb Q(\!(q)\!)$ is generated over $\mathbb Q$ by the quotients $q$-expansion-of-$p_f$ over $q$-expansion-of-$p_g$ attached to integral $q$-expansions of modular forms of weight $k$ for $\Gamma$; let $E$ be the analogous field over $\overline{\mathbb Q}$ inside $\overline{\mathbb Q}(\!(q)\!)$. Let $O$ be a valuation subring of $E$ consisting exactly of those $f$ for which there are Laurent series $x,y$ over $A$ with the coefficientwise reduction of $y$ modulo the maximal ideal of $A$ non-zero and $f\cdot y=x$ in $\overline{\mathbb Q}(\!(q)\!)$, and let $\varphi:K\to E$ be a ring homomorphism acting coefficientwise by the inclusion $K_1\subseteq\overline{\mathbb Q}$. Then for every $f\in O$ there is $w\in K$ with $\varphi(w)\in O$ and $f-\varphi(w)$ a non-unit of $O$, i.e. in the maximal ideal of $O$.
--
--   This is the statement that the constant extension from $K_1$ to $\overline{\mathbb Q}$ produces no residual defect for the Gauss valuation ring of $A$-integral $q$-expansions: modulo the maximal ideal of $O$, the image of $\varphi$ already exhausts $O$, so the residue field of $O$ coincides with that of $O\cap\varphi(K)$. It rests on the construction of the regular prolongation of $A$ to the base-changed $q$-expansion function field, and it feeds the comparison of points read off the two-chart integral models of the modular curve of full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)

    (hκ₁ : Function.Surjective
      (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ (a : ↥K₁)).mp a.2⟩))
    (K : IntermediateField ↥K₁ (LaurentSeries ↥K₁))
    (hK : K = ModularCurve.laurentBaseChange ↥K₁ (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hE : E = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))

    (O : ValuationSubring ↥E)
    (hO : ∀ f : ↥E, f ∈ O ↔ ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (φ : ↥K →+* ↥E)
    (hφ : ∀ f : ↥K, ((φ f : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((f : ↥K) : LaurentSeries ↥K₁)) :
    ∀ f : ↥E, f ∈ O → ∃ w : ↥K, φ w ∈ O ∧ (f - φ w : ↥E) ∈ O.nonunits := by sorry
