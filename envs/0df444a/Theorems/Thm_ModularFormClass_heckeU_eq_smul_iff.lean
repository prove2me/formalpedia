-- Prove2me | Theorems.Thm_ModularFormClass_heckeU_eq_smul_iff
-- name    : ModularFormClass.heckeU_eq_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/4ff5b292-4112-5792-b674-0767676f608c
-- title:
--   Uₚ f = c f iff aₙₚ = c aₙ for all n
-- statement:
--   Let $F$ be a type equipped with a coercion to functions $\mathbb{H} \to \mathbb{C}$, let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$, let $k \in \mathbb{Z}$, and assume $F$ is a class of modular forms of weight $k$ for $\Gamma$; let $f : F$. Assume the real number $1$ belongs to $\Gamma.\mathrm{strictPeriods}$, so that the function $z \mapsto f(z)$ is $1$-periodic and bounded as $\operatorname{Im} z \to \infty$, and hence has a $q$-expansion of period $1$ whose $n$-th coefficient is written $\mathrm{qCoeff}\, f\, n$. Let $p$ be a natural number with $p \neq 0$ and let $c \in \mathbb{C}$. Write $\mathrm{heckeU}\,k\,p\,f = \sum_{j=0}^{p-1} f \mid_k \begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}$, the sum of weight-$k$ slash actions of the upper triangular matrices $\mathrm{heckeMatrix}\,p\,j$. The assertion is that the equality $\mathrm{heckeU}\,k\,p\,f = c \cdot f$ of functions on the upper half-plane holds if and only if $\mathrm{qCoeff}\, f\, (np) = c \cdot \mathrm{qCoeff}\, f\, n$ for every natural number $n$, the left-hand side being $\mathrm{coeffHeckeU}\,p$ applied to the coefficient sequence of $f$ at $n$.
--
--   This is the standard translation of the eigenvalue equation for the Hecke operator $U_p$ on modular forms with a $q$-expansion at $\infty$ into a relation among Fourier coefficients, $a_{np} = c\,a_n$. It is used downstream in the linear-operator form of the same criterion and in the characterisation of normalised eigenforms through the coefficient recursions at primes dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularFormClass_heckeU_eq_smul_iff.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularFormClass.heckeU_eq_smul_iff {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) : ModularForm.heckeU k p ⇑f = c • ⇑f ↔ ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by sorry
