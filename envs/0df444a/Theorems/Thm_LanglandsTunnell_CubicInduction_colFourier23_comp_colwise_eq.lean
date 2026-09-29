-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_colFourier23_comp_colwise_eq
-- name    : LanglandsTunnell.CubicInduction.colFourier23_comp_colwise_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/05d2deaa-12cb-5237-95a9-761602d51bc1
-- title:
--   Covariance of the column Fourier transform under column-wise substitutions
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, with completion $F = \mathbb{Q}_v$ carried by its Borel $\sigma$-algebra, let $\eta$ be an additive character of $F$ with values in $\mathbb{C}$, let $j \in \{0,1,2\}$, let $A : \{0,1,2\} \to \mathrm{GL}_2(F)$ be a triple of invertible $2\times 2$ matrices over $F$, let $\rho : M_{2\times 3}(F) \to \mathbb{C}$ be an arbitrary function (no measurability or decay assumption), and let $X \in M_{2\times 3}(F)$. Here `colFourier23 v η j Φ X` denotes $\int_{F\times F} \Phi(\mathrm{setCol23}\,X\,j\,u)\, \eta(u_1 X_{0j} + u_2 X_{1j})\, du$, the integral being taken against the product of two copies of the self-dual Haar measure at $v$ (the additive Haar measure on the local integers rescaled by $(\mathrm{absNorm}\, v)^{-\mathrm{level}/2}$), and $\mathrm{setCol23}\,X\,j\,u$ being $X$ with its $j$-th column replaced by $(u_1,u_2)^{t}$. The assertion is that the column-$j$ Fourier transform of the function $Y \mapsto \rho\big((A_k Y_k)_k\big)$, whose $(i,k)$ entry is $\sum_{i'} (A_k)_{ii'} Y_{i'k}$, evaluated at $X$, equals $\mathrm{modulus}(\det A_j)^{-1}$ — the module of $\det A_j \in F$, realised as a real number and coerced to $\mathbb{C}$ — times the column-$j$ Fourier transform of $\rho$ evaluated at the matrix with $(i,k)$ entry $\sum_{i'} (A'_k)_{ii'} X_{i'k}$, where $A'$ is $A$ with its $j$-th member updated to $\mathrm{transposeInvN}(A_j) = (A_j^{-1})^{t}$ (the unit with value $(A_j^{-1})^{t}$ and inverse $A_j^{t}$).
--
--   This is the local covariance of the partial (column-$j$) Fourier transform on $2\times 3$ matrices under column-wise left multiplication: the substitution is absorbed by scaling by the module of the determinant and by replacing the $j$-th matrix by its inverse transpose, the remaining columns being untouched. It is applied repeatedly in the Godement-section part of the cubic induction, in [`LanglandsTunnell.CubicInduction.matFourier22_comp_inv_mul_eq`](thm.html#LanglandsTunnell.CubicInduction.matFourier22_comp_inv_mul_eq), [`LanglandsTunnell.CubicInduction.matFourier22_comp_mul_right_eq`](thm.html#LanglandsTunnell.CubicInduction.matFourier22_comp_mul_right_eq) and [`LanglandsTunnell.CubicInduction.matFourier23_comp_mul_mul_eq`](thm.html#LanglandsTunnell.CubicInduction.matFourier23_comp_mul_mul_eq), to compute how the full matrix Fourier transform transforms under left and right translations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_colFourier23_comp_colwise_eq.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.colFourier23_comp_colwise_eq
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 3)
    (A : Fin 3 → GL (Fin 2) (v.adicCompletion ℚ))
    (ρ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) :
    colFourier23 v η j (fun Y => ρ (Matrix.of fun i k =>
        ∑ i' : Fin 2, ((A k : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i i' * Y i' k)) X =
      ((modulus ((Matrix.GeneralLinearGroup.det (A j) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ *
        colFourier23 v η j ρ (Matrix.of fun i k =>
          ∑ i' : Fin 2, ((Function.update A j (transposeInvN (Fin 2) (A j)) k : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i i' * X i' k) := by sorry
