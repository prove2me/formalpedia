-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_cellSectionOf_antidiagonal3_mul_mul_eq_integral_godementDatum
-- name    : LanglandsTunnell.CubicInduction.cellSectionOf_antidiagonal3_mul_mul_eq_integral_godementDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/0a37a247-809c-5710-bc45-5e8137bbdbf0
-- title:
--   Big-cell GL₃ section as a GL₂ Godement integral
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), write $F = \mathbb{Q}_p$ for the completion, let $\lambda_0,\lambda_1,\lambda_2 : F^{\times} \to \mathbb{C}^{\times}$ be group homomorphisms, let $\Phi : F^3 \to \mathbb{C}$ be an arbitrary function and let $T \in GL_3(F)$. With $GL_2(F)$ and $F$ carrying their Borel $\sigma$-algebras, let $\mu_2$ be a Haar measure on $GL_2(F)$, let $K \le GL_2(F)$ be a subgroup whose underlying set is open and compact, and let $\varphi : M_{2\times 3}(F) \to GL_2(F) \to \mathbb{C}$ be given by the closed formula: for $X \in M_{2\times3}(F)$ and $g \in GL_2(F)$, putting $Z = XT$, $s$ the $2\times2$ block formed by the first two columns of $Z$, and $N = gZ$,
--   $$\varphi_X(g) = \mu_2(K)^{-1}\,\lambda_0(\det T)\,|\det T|\;\mathbf{1}_{K}(s)\;\lambda_0(\det s)^{-1}\,\|\det s\|^{-1}\,|\det g|^{1/2}\,\lambda_1\!\left(\tfrac{\det g \cdot \det s}{N_{10}}\right)\lambda_2(N_{10})\,\|N_{10}\|^{-1}\,\Phi\!\left(\tfrac{N_{11}}{N_{10}},\tfrac{N_{12}}{N_{10}},\tfrac{Z_{00}Z_{12}-Z_{02}Z_{10}}{\det s}\right),$$
--   where $\mathbf{1}_K$ is the indicator of the set of matrices underlying elements of $K$, each $\lambda_i(x)$ is read as $0$ when $x = 0$, and $|\cdot|$ denotes `modulus`, the module of the multiplication action on Haar measure. Then for every $Y \in GL_3(F)$, writing $w_2 = \begin{pmatrix}0&1\\1&0\end{pmatrix}$, $w_3$ for the $3\times3$ antidiagonal permutation matrix, $(h\mid 0)$ for the $2\times3$ matrix with $h$ in the first two columns and zero last column, and
--   $$F(h) = \varphi_{(h\mid 0)Y}\bigl(w_2 h^{-1}\bigr)\,\lambda_0(\det h)\,|\det h|^{3/2},$$
--   the function $F$ is $\mu_2$-integrable,
--   $$f_{\lambda,\Phi}(w_3 Y T) = \lambda_0(\det Y)\,|\det Y| \int_{GL_2(F)} F(h)\,d\mu_2(h),$$
--   and $\int \|F(h)\|\,d\mu_2(h) = \|f_{\lambda,\Phi}(w_3YT)\|\cdot\bigl(\|\lambda_0(\det Y)\|\,|\det Y|\bigr)^{-1}$. Here $f_{\lambda,\Phi} =$ `cellSectionOf p lam Φ` is the function supported on the big cell $\{\,$corner entry $\neq 0$, lower minor $\neq 0\,\}$ of $GL_3(F)$ given there by $\lambda_0(\det g/\mathrm{lm}(g))\lambda_1(\mathrm{lm}(g)/\mathrm{ce}(g))\lambda_2(\mathrm{ce}(g))\,(\|\det g/\mathrm{lm}(g)\|/\|\mathrm{ce}(g)\|)\,\Phi(\mathrm{cellRatio}(g))$.
--
--   The statement identifies a translate of the big-cell section of a $GL_3$ principal series with the Godement-type integral over $GL_2(F)$ of the explicit local datum, with no chamber condition on the quasi-characters and no regularity assumption on $\Phi$; the accompanying norm identity is what makes the integral absolutely convergent. It feeds the comparison of the $GL_3$ Jacquet–Whittaker function with the Godement–Whittaker construction in [`LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber`](thm.html#LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber), part of the local input to the Rankin–Selberg and converse-theorem machinery used for Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_cellSectionOf_antidiagonal3_mul_mul_eq_integral_godementDatum.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

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

theorem LanglandsTunnell.CubicInduction.cellSectionOf_antidiagonal3_mul_mul_eq_integral_godementDatum
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ)
    (T : LocalGL3 p) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
    ∀ (φsec : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (φsec = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) =>
        let Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
        let s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := Matrix.of fun i j => Z i (Fin.castSucc j)
        let N : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z
        ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
          (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ)) s *
          (charExt (lam 0) s.det)⁻¹ * ((‖s.det‖⁻¹ : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ) *
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s.det / N 1 0) *
          charExt (lam 2) (N 1 0) * ((‖N 1 0‖⁻¹ : ℝ) : ℂ) *
          Φ ![N 1 1 / N 1 0, N 1 2 / N 1 0, (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) / s.det]) →
    ∀ Y : LocalGL3 p,
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          φsec ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
              (antidiagonal2 p * h⁻¹) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ)) μ₂ ∧
      cellSectionOf p lam Φ (antidiagonal3 p * Y * T) =
        ((lam 0 (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
          ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
            φsec ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
              (antidiagonal2 p * h⁻¹) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ) ∂μ₂ ∧
      ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
          ‖φsec ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
              (antidiagonal2 p * h⁻¹) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ)‖ ∂μ₂ =
        ‖cellSectionOf p lam Φ (antidiagonal3 p * Y * T)‖ *
          (‖((lam 0 (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ)‖ * ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)))⁻¹ := by sorry
