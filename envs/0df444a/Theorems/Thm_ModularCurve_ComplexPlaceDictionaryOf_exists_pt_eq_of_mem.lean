-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
-- name    : ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/febd49ec-8cd8-5f08-878f-9a85778d4061
-- title:
--   Every place where j is regular is a point place
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$ containing $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, and let $F_0$ be an intermediate field of $\mathbb{Q}\subseteq\mathbb{Q}((q))$ that equals [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients of $q$-expansions of pairs of modular forms of equal weight for $\Gamma$ having integral $q$-expansions (with nonzero denominator). Write $\mathbb{C}F_0$ for [`ModularCurve.laurentBaseChange ℂ F₀`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the image of $F_0$ under coefficientwise extension of scalars. Let $D$ be a complex place dictionary for $(\Gamma,F_0)$, i.e. a map $\mathrm{pt}$ from the upper half-plane to the places of $\mathbb{C}F_0$ over $\mathbb{C}$ (valuation subrings containing $\mathbb{C}$, proper, and principal ideal rings) together with positive integers $e_\tau$, such that $\mathrm{pt}$ is $\Gamma$-invariant, $x$ lies in the valuation subring of $\mathrm{pt}(\tau)$ exactly when $z\mapsto\|\mathrm{realizeOf}\,\Gamma\,x\,z\|$ is bounded near $\tau$ on the punctured neighbourhood filter, and for $x\neq 0$ the meromorphic order of the realisation at $\tau$ is $e_\tau\cdot\mathrm{ord}_{\mathrm{pt}(\tau)}(x)$. Let $P$ be a place of $\mathbb{C}F_0$ over $\mathbb{C}$ and let $x\in\mathbb{C}F_0$ have underlying Laurent series $q^{-1}\cdot(E_4^3/\Delta$-numerator series$)$, i.e. [`ModularCurve.jqModC ℂ`](def/ModularCurve_JqCoeff.html#L15). If $x$ lies in the valuation subring of $P$, then $P=\mathrm{pt}(\tau)$ for some $\tau$ in the upper half-plane.
--
--   This is the completeness half of the identification of $\Gamma\backslash\mathfrak{H}$ with the places of the function field of $X(\Gamma)$ at which $j$ is regular: a place not lying above $j=\infty$, i.e. not a cusp, is the place attached to a point of the upper half-plane. It is used in the comparison of ramification indices with stabiliser orders, in the computation of Hecke correspondences on divisors supported at point places, and in the Abel–Jacobi criterion for principality of such divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀)
    (P : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀))
    (x : ModularCurve.laurentBaseChange ℂ F₀) (hx : (x : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hP : x ∈ P.toValuationSubring) :
    ∃ τ : UpperHalfPlane, D.pt τ = P := by sorry
