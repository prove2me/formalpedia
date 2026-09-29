-- Prove2me | Theorems.Thm_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent
-- name    : ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/30967da8-1346-5359-8a84-415f82320705
-- title:
--   Linear independence of Laurent series under coefficient field extension
-- statement:
--   Let $\kappa$ and $k$ be fields with $k$ a $\kappa$-algebra, let $n$ be a natural number, and let $f : \mathrm{Fin}\,n \to \kappa(\!(q)\!)$ be a finite family of formal Laurent series with coefficients in $\kappa$ (the Mathlib type `LaurentSeries κ` of Hahn series over $\kappa$ with value group $\mathbb{Z}$). Assume that $f$ is linearly independent over $\kappa$. Then the family obtained by composing $f$ with the underlying function of `coeffMap (algebraMap κ k)` — the ring homomorphism $\kappa(\!(q)\!) \to k(\!(q)\!)$ that applies the structure map $\kappa \to k$ to each coefficient, i.e. sends a series to its image under `HahnSeries.map` along $\mathrm{algebraMap}\,\kappa\,k$ — is linearly independent over $k$. Equivalently: if $a_1,\dots,a_n \in k$ satisfy $\sum_i a_i \cdot \Phi(f_i) = 0$ in $k(\!(q)\!)$, where $\Phi$ is the coefficientwise map, then all $a_i$ vanish.
--
--   This is the statement that $k$ and $\kappa(\!(q)\!)$ are linearly disjoint over $\kappa$ inside $k(\!(q)\!)$, equivalently that the natural map $k \otimes_\kappa \kappa(\!(q)\!) \to k(\!(q)\!)$ is injective, in the form of preservation of linear independence of finite families. It is used in the analysis of $q$-expansions of functions on modular and Igusa curves, where base change of a coefficient field must be recognised inside a Laurent series field; several results about models of $X_1$ and their special fibres cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    {n : ℕ} (f : Fin n → LaurentSeries κ) (hf : LinearIndependent κ f) :
    LinearIndependent k (⇑(coeffMap (algebraMap κ k)) ∘ f) := by sorry
