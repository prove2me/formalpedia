-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_psiLocal_mul_transposeInvN_eq_mul_integral_psiLocal_mul_dual
-- name    : LanglandsTunnell.CubicInduction.integral_psiLocal_mul_transposeInvN_eq_mul_integral_psiLocal_mul_dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/81292728-e326-5077-bcab-72c8f7f65f0d
-- title:
--   Dual Jacquet integral of a principal-series vector
-- statement:
--   Let $p$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the completion of $\mathbb{Q}$ at $p$, and let $\mu = (\mu_0,\mu_1)$ be a pair of multiplicative characters $F^\times \to \mathbb{C}^\times$ (monoid homomorphisms, with no continuity assumed). Let $\varphi : \mathrm{GL}_2(F) \to \mathbb{C}$ lie in `principalSeries2`, that is: $\varphi$ is locally constant, $\varphi(n(x)h) = \varphi(h)$ for all $x \in F$ and $h$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and $\varphi(\mathrm{diag}(a_0,a_1)h) = \mu_0(a_0)\mu_1(a_1)\,(\lVert a_0\rVert/\lVert a_1\rVert)^{1/2}\,\varphi(h)$ for units $a_0,a_1$. Let $w_0 \in \mathrm{GL}_2(F)$ be an element whose underlying matrix is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and let $g \in \mathrm{GL}_2(F)$ be arbitrary. Then, with respect to the self-dual additive Haar measure $dx$ on $F$ (the Haar measure giving the valuation ring measure $(\mathrm{N}p)^{-n/2}$, $n$ the level of the local component $\psi_p$ of the standard adelic additive character of $\mathbb{Q}$), $$\int_F \psi_p(x)\,\varphi\bigl(w\,n(x)\,w_0\,{}^t g^{-1}\bigr)\,dx = \mu_1(-1)\int_F \psi_p(x)\,\varphi\bigl(w_0\,{}^t\bigl(w\,n(x)\,\mathrm{diag}(1,-1)\,g\,w_0\bigr)^{-1} w_0\bigr)\,dx,$$ where $w$ denotes `antidiagonal2`, the element of $\mathrm{GL}_2(F)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and ${}^t(\cdot)^{-1}$ is the transpose-inverse involution `transposeInvN`.
--
--   The identity compares the raw local Jacquet (Whittaker) integral of a principal-series vector $\varphi$ at $w\,{}^tg^{-1}$ with that of the dual vector $\varphi^\vee(h) = \varphi(w\,{}^th^{-1}w)$ at $\mathrm{diag}(1,-1)\,g\,w$; it is the rank-one counterpart of the corresponding $\mathrm{GL}_3$ statement, and is asserted for the Bochner integrals as written, without any convergence or chamber hypothesis. It is used in the local Rankin–Selberg computations for principal-series vectors, both in the cuspidal case and in the case of a Borel eigenfunctional, and in the $\mathrm{GL}_3 \times \mathrm{GL}_2$ chamber identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_psiLocal_mul_transposeInvN_eq_mul_integral_psiLocal_mul_dual.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.CubicInduction.integral_psiLocal_mul_transposeInvN_eq_mul_integral_psiLocal_mul_dual
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
        φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) =
      ((μ 1 (-1) : ℂˣ) : ℂ) *
        ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
          φ (w₀p * transposeInvN (Fin 2) (antidiagonal2 p * upperUnipotent2 p x * (diagonal2 p ![1, -1] * g * w₀p)) * w₀p)
          ∂(selfDualHaarAt ℚ p) := by sorry
