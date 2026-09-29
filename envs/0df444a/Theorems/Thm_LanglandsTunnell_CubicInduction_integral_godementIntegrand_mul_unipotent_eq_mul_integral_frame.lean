-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame
-- name    : LanglandsTunnell.CubicInduction.integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/860d1ecd-678c-5403-b937-75aa8f0719fb
-- title:
--   Unipotent fibre integration of the GL₃ Godement integrand
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, with completion $F = \mathbb{Q}_v$, let $\theta$ be an additive character of $F$ with values in $\mathbb{C}$, and let $n \in \mathbb{Z}$ be such that $\theta$ is trivial on $\{x : v(x) \le \exp n\}$ while some $x$ with $v(x) \le \exp(n+1)$ has $\theta(x) \ne 1$, i.e. $\theta$ has exact level $n$. Let $\mathrm{lam} : F^{\times} \to \mathbb{C}^{\times}$ be a group homomorphism, and let $\Psi$ assign to a $2 \times 3$ matrix $X$ over $F$ and a $k \in GL_2(F)$ a complex number, such that for each $k$ the function $X \mapsto \Psi(X,k)$ is locally constant with compact support, and such that $\Psi(X, u(a)k) = \theta(a)\,\Psi(X,k)$ for all $X$, all $a \in F$ and all $k$, where $u(a) = \begin{pmatrix}1&a\\0&1\end{pmatrix}$ is `unipotentGL2 a`. Fix $M \in GL_3(F)$ and $h \in GL_2(F)$. The assertion is an identity of integrals taken with respect to the self-dual additive Haar measure $\mu$ on $F$ (the Haar measure of the ring of integers scaled by $q_v^{-\ell/2}$, $\ell$ the level of the standard local character) and, on the right, with respect to `jacquetHaar3`, the threefold product $\mu \otimes \mu \otimes \mu$ on $F \times F \times F$; the Borel $\sigma$-algebra is used throughout. Namely,
--   $$\int_F \mathcal{Q}\bigl(X \mapsto \Psi(XM, (h\,u(a))^{-1})\bigr)\bigl(A(h\,u(a))\bigr)\; \mathrm{lam}(\det(h\,u(a)))\; |\det(h\,u(a))|^{1/2}\,d\mu(a)$$
--   equals
--   $$\mathrm{lam}(\det h)\,|\det h|^{1/2}\,|\det h| \int_{F^3} \Psi\Bigl(h \begin{pmatrix}1&t_1&t_2\\0&1&t_3\end{pmatrix} M,\; h^{-1}\Bigr)\,\theta(-(t_1+t_3))\,d(t_1,t_2,t_3).$$
--   Here $|\cdot|$ denotes `modulus`, the module of the Haar measure under multiplication (equal to the normalised absolute value on $F$), raised to the complex exponent $1/2$ in the first occurrence; $A(k) =$ `godementArg v k` is the $2 \times 3$ matrix whose first two columns are those of $k$ and whose last column is the second column of ${}^t k^{-1}$; and $\mathcal{Q} =$ `rowFourier23 v θ⁻¹` is the partial Fourier transform in the last column, $\mathcal{Q}(\Phi)(X) = \int_{F^2} \Phi(X \text{ with last column replaced by } u)\,\theta^{-1}(u_1 X_{0,2} + u_2 X_{1,2})\,d(u_1,u_2)$.
--
--   This is the unfolding step for the Godement-type section attached to a $2 \times 3$ Schwartz–Bruhat datum: integration of the $GL_3$ Whittaker integrand along the unipotent direction $h \mapsto h\,u(a)$ collapses the partial Fourier transform in the last column into a Jacquet-style integral over the three-parameter frame $\begin{pmatrix}1&t_1&t_2\\0&1&t_3\end{pmatrix}$, at the cost of the Jacobian factor $|\det h|$. It is used in the Rankin–Selberg step comparing the $GL_3$ Godement–Whittaker function with that of the dual Fourier transform of the datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.StandardAddChar

theorem LanglandsTunnell.CubicInduction.integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame
    (v : HeightOneSpectrum (𝓞 ℚ)) (θ : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hθn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → θ x = 1)
    (hθn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ θ x ≠ 1)
    (lam : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (Ψ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hΨsb : ∀ k : GL (Fin 2) (v.adicCompletion ℚ), IsSchwartzBruhat (fun X => Ψ X k))
    (hΨlaw : ∀ (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (a : v.adicCompletion ℚ)
      (k : GL (Fin 2) (v.adicCompletion ℚ)), Ψ X (unipotentGL2 a * k) = θ a * Ψ X k)
    (M : GL (Fin 3) (v.adicCompletion ℚ)) (h : GL (Fin 2) (v.adicCompletion ℚ)) :
    letI := localBorel ℚ v
    ∫ a : v.adicCompletion ℚ,
        rowFourier23 v θ⁻¹
            (fun X => Ψ (X * ((M : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))
              (h * unipotentGL2 a)⁻¹)
            (godementArg v (h * unipotentGL2 a))
          * ((lam (Matrix.GeneralLinearGroup.det (h * unipotentGL2 a)) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det (h * unipotentGL2 a) : (v.adicCompletion ℚ)ˣ) :
              v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂(selfDualHaarAt ℚ v) =
      ((lam (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
        * ∫ t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
            Ψ (((h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
                !![1, t.1, t.2.1; 0, 1, t.2.2] *
                ((M : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) h⁻¹ *
              θ (-(t.1 + t.2.2)) ∂(jacquetHaar3 v) := by sorry
