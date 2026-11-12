-- Prove2me | Theorems.Thm_IsotropicSpin_eq_21
-- name    : IsotropicSpin.eq_21
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:26:13.067319+00:00
-- url     : https://prove2.me/theorems/f75ade92-51aa-4dfc-b115-03e149a6a19d
-- title:
--   Eqs. (20)–(21) — the matrix $ZZ^\dagger$ and its eigenvalue $\lambda=1$
-- statement:
--   For real $\alpha,\beta$ put $a=\cos\alpha$, $b=\sin\alpha\cos\beta$, $c=\tfrac1{\sqrt2}\sin\alpha\sin\beta$ (20), and let $Z$ be the matrix (19) built from the spin-1 matrices (13). Then
--
--   1. $a^2+b^2+2c^2=1$;
--   2. $$ZZ^\dagger=\begin{pmatrix}a^2+b^2+c^2&-ic(a+ib)&c^2\\ ic(a-ib)&2c^2&-ic(a-ib)\\ c^2&ic(a+ib)&a^2+b^2+c^2\end{pmatrix},$$ the matrix whose characteristic polynomial $W(\lambda)$ is the first determinant in (21);
--   3. $\lambda=1$ is an eigenvalue of $ZZ^\dagger$: $\det(\mathbf 1-ZZ^\dagger)=0$.
--
--   With $\operatorname{tr}ZZ^\dagger=2$ and positivity, this gives $\|ZZ^\dagger\|=1$.
--
--   **Formalization Note** `Matrix.charpoly` is $\det(\lambda\mathbf 1-M)$, which vanishes at the same $\lambda$ as the page's $W(\lambda)=\det(M-\lambda\mathbf 1)$.
--
--   Differences from the source:
--   - encoding: W(λ) = det(ZZ† − λ1) and "λ = 1 is an eigenvalue" → (ZZ†).charpoly.eval 1 = 0, charpoly = det(λ1 − ZZ†); reason: the two determinants differ by the sign (−1)³ and vanish at the same λ
--   - reading: the second determinant of (21), printed with elided rows "..." → not stated; its consequence, λ = 1 is an eigenvalue, is clause 3; reason: the elided entries are a step of the computation, not a claim; the claim it supports is kept
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eqs. (20)–(21), pp.2–3

import Mathlib
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_zMat

open scoped Matrix

namespace IsotropicSpin

/-- **`ZZ†` and its eigenvalue `1`**, Alicki, arXiv:quant-ph/0402080v1, eqs. (20)–(21), pp. 2–3.
For real `α, β` put `a = cos α`, `b = sin α cos β`, `c = (1/√2) sin α sin β` (20). Then

1. `a² + b² + 2c² = 1` (20);
2. `Z Z† = !![a²+b²+c², −ic(a+ib), c²; ic(a−ib), 2c², −ic(a−ib); c², ic(a+ib), a²+b²+c²]`, the
   matrix whose characteristic polynomial `W(λ)` is the first determinant of (21);
3. `λ = 1` is an eigenvalue of `Z Z†`: `W(1) = det(Z Z† − 𝟙) = 0`.

**Formalization Note** `1/√2` is `(√2)⁻¹`. `Matrix.charpoly` is `det(λ𝟙 − M)`, which vanishes at
the same `λ` as the page's `W(λ) = det(M − λ𝟙)`. -/
theorem eq_21 (α β : ℝ) :
    (Real.cos α) ^ 2 + (Real.sin α * Real.cos β) ^ 2 +
        2 * ((Real.sqrt 2)⁻¹ * Real.sin α * Real.sin β) ^ 2 = 1 ∧
    zMat α β * (zMat α β)ᴴ =
      (let a : ℂ := Real.cos α
       let b : ℂ := Real.sin α * Real.cos β
       let c : ℂ := (Real.sqrt 2)⁻¹ * Real.sin α * Real.sin β
       !![a ^ 2 + b ^ 2 + c ^ 2, -Complex.I * c * (a + Complex.I * b), c ^ 2;
          Complex.I * c * (a - Complex.I * b), 2 * c ^ 2, -Complex.I * c * (a - Complex.I * b);
          c ^ 2, Complex.I * c * (a + Complex.I * b), a ^ 2 + b ^ 2 + c ^ 2]) ∧
    (zMat α β * (zMat α β)ᴴ).charpoly.eval 1 = 0 := by sorry

end IsotropicSpin
