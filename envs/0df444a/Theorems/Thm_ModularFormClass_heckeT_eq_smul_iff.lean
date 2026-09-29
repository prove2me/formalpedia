-- Prove2me | Theorems.Thm_ModularFormClass_heckeT_eq_smul_iff
-- name    : ModularFormClass.heckeT_eq_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d7b50ef1-3cc8-5b5f-ae80-34b7b12e832e
-- title:
--   Tₚ f = c f tested on q-expansion coefficients
-- statement:
--   Let $F$ be a type with a `FunLike` coercion to functions $\mathbb{H} \to \mathbb{C}$, let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$, let $k \in \mathbb{Z}$, and assume $F$ is a class of modular forms of weight $k$ for $\Gamma$ (`ModularFormClass F Γ k`). Let $f : F$, and assume the real number $1$ lies in `Γ.strictPeriods`, so that the underlying function of $f$ is $1$-periodic in the variable on $\mathbb{H}$ and $\infty$ is a cusp of $\Gamma$, whence $f$ is bounded towards $i\infty$. Let $p$ be a natural number with $p \neq 0$ and $c \in \mathbb{C}$. Write $a_n =$ `qCoeff f n`, the $n$-th coefficient of the $q$-expansion `qExpansion 1 ⇑f` of $f$ with respect to the period $1$. The assertion is the equivalence of: (i) the equality of functions on $\mathbb{H}$
--   $$\mathrm{heckeT}\,k\,p\,f \;=\; \sum_{j < p} f \mid[k]\, \mathrm{heckeMatrix}\,p\,j \;+\; f \mid[k]\,\mathrm{diag}(p,1) \;=\; c \cdot f,$$
--   where $\mathrm{diag}(p,1)$ is `heckeDiagMatrix p`, namely `upperTriangularGL p 0 1` since $p \neq 0$; and (ii) the coefficientwise identity $a_{np} + \bigl[p \mid n\bigr]\,p^{\,k-1} a_{n/p} = c\,a_n$ for every $n \in \mathbb{N}$, the left-hand side being `coeffHeckeT k p (qCoeff f) n`.
--
--   This is the standard dictionary between a Hecke eigenvalue equation $T_p f = c f$, read as an identity of functions on the upper half-plane built from slash actions of the usual coset representatives, and the recursion $a_{np} + p^{k-1}a_{n/p} = c\,a_n$ on $q$-expansion coefficients. It is the bridge used by [`CuspForm.heckeTLin_apply_eq_smul_iff`](thm.html#CuspForm.heckeTLin_apply_eq_smul_iff) and by [`CuspForm.isNormalizedEigenform_iff_heckeT`](thm.html#CuspForm.isNormalizedEigenform_iff_heckeT), where normalised eigenforms are characterised through their coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularFormClass_heckeT_eq_smul_iff.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularFormClass.heckeT_eq_smul_iff {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) : ModularForm.heckeT k p ⇑f = c • ⇑f ↔ ∀ n : ℕ, ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by sorry
