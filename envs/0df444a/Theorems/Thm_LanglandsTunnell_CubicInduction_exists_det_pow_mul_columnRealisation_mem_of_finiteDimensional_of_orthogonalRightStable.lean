-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable
-- name    : LanglandsTunnell.CubicInduction.exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/aa3e6b27-fcad-5b2d-a7e8-f33cbbc0e991
-- title:
--   Right O(3)-stable spaces contain det^α times a column harmonic
-- statement:
--   Fix a column index $j \in \{0,1,2\}$ and a complex subspace $E$ of the space of functions $\mathrm{M}_3(\mathbb{R}) \to \mathbb{C}$, finite-dimensional over $\mathbb{C}$, such that some $F \in E$ is non-zero at some $r \in \mathrm{O}(3)$ and such that for all $F \in E$ and $r_0 \in \mathrm{O}(3)$ the right translate $r \mapsto F(r r_0)$ again lies in $E$. Write $R_{c_1 c_2}(s)$ for the matrix with $\cos s$ at the two diagonal entries $(c_1,c_1)$, $(c_2,c_2)$, with $-\sin s$ at $(c_1,c_2)$ and $\sin s$ at $(c_2,c_1)$, and the identity elsewhere, and index the three planes $(0,1),(0,2),(1,2)$ by $c \in \{0,1,2\}$. The assertion is: for every triple $L_0,L_1,L_2$ of $\mathbb{C}$-linear endomorphisms of $E$ such that, for all $F \in E$, all $c$ and all $r \in \mathrm{O}(3)$, the function $s \mapsto F(r R_c(s))$ has derivative $(L_c F)(r)$ at $s = 0$, and such that on $\mathrm{O}(3)$ the commutators satisfy $[L_0,L_1]F = L_2 F$, $[L_0,L_2]F = -L_1 F$, $[L_1,L_2]F = L_0 F$, there exist $\alpha \in \{0,1\}$, $\ell \in \mathbb{N}$ and a non-zero $p \in \mathbb{C}[x_0,x_1,x_2]$, homogeneous of degree $\ell$ with $\sum_i \partial_i^2 p = 0$, together with $F \in E$ satisfying $F(r) = \det(r)^{\alpha} \, p(r_{0j}, r_{1j}, r_{2j})$ for all $r \in \mathrm{O}(3)$. Since the conclusion does not involve $L$, the statement amounts to the implication from the existence of one such triple.
--
--   This is the harmonic-polynomial description of the functions occurring in a finite-dimensional right-translation-stable space on $\mathrm{O}(3)$: the infinitesimal rotation operators in the three coordinate planes, satisfying the $\mathfrak{so}(3)$ commutation relations, force a member of the space to be a power of the determinant times a harmonic form in a single column. It is used in the analysis of sign-isotypic vectors, feeding the two statements [`LanglandsTunnell.CubicInduction.exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero`](thm.html#LanglandsTunnell.CubicInduction.exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero) and [`LanglandsTunnell.CubicInduction.exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero`](thm.html#LanglandsTunnell.CubicInduction.exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.lean

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Matrix.Notation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
LanglandsTunnell.CubicInduction.exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable
    (j : Fin 3) (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) [FiniteDimensional ℂ E]
    (hne : ∃ F ∈ E, ∃ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, F r ≠ 0)
    (hstab : ∀ F ∈ E, ∀ r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ, (fun r => F (r * r₀)) ∈ E) :
    let rot : Fin 3 → Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun c₁ c₂ s => Matrix.of fun i k =>
      if i = c₁ ∧ k = c₁ then Real.cos s else if i = c₂ ∧ k = c₂ then Real.cos s else
      if i = c₁ ∧ k = c₂ then - Real.sin s else if i = c₂ ∧ k = c₁ then Real.sin s else
      if i = k then (1 : ℝ) else 0
    let planes : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]
    let val : E → Matrix (Fin 3) (Fin 3) ℝ → ℂ := fun F => (F : Matrix (Fin 3) (Fin 3) ℝ → ℂ)
    let realise : MvPolynomial (Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun q => MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q
    ∀ L : Fin 3 → Module.End ℂ E,
      (∀ (F : E) (c : Fin 3), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        HasDerivAt (fun s : ℝ => val F (r * rot (planes c).1 (planes c).2 s)) (val (L c F) r) 0) →
      (∀ (F : E), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        val (L 0 (L 1 F)) r - val (L 1 (L 0 F)) r = val (L 2 F) r ∧
        val (L 0 (L 2 F)) r - val (L 2 (L 0 F)) r = - val (L 1 F) r ∧
        val (L 1 (L 2 F)) r - val (L 2 (L 1 F)) r = val (L 0 F) r) →
      ∃ (α : Fin 2) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ), p ≠ 0 ∧
      p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 ∧
      ∃ F ∈ E, ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        F r = ((r.det : ℝ) : ℂ) ^ (α : ℕ) *
          MvPolynomial.eval (fun ab : Fin 3 × Fin 3 => ((r ab.1 ab.2 : ℝ) : ℂ)) (realise p) := by sorry
