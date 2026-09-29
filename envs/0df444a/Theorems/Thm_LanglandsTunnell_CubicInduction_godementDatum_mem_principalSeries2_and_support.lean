-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_godementDatum_mem_principalSeries2_and_support
-- name    : LanglandsTunnell.CubicInduction.godementDatum_mem_principalSeries2_and_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/6843e40f-6ed3-59aa-a9c6-bcb610be4c69
-- title:
--   Godement slot vectors: principal series membership and support
-- statement:
--   Let $p$ be a nonzero prime of $\mathcal O_{\mathbb Q}$ with completion $F=\mathbb Q_p$, let $\lambda_0,\lambda_1,\lambda_2\colon F^\times\to\mathbb C^\times$ be locally constant homomorphisms, let $\Phi\colon F^3\to\mathbb C$ be locally constant with compact support, and let $T\in GL_3(F)$; $F$, $M_{2\times 3}(F)$ and $GL_2(F)$ carry their Borel structures. Then there are an open $U\subseteq GL_2(F)$ with $1\in U$ and a real $R$ such that for every Haar measure $\mu_2$ on $GL_2(F)$, every subgroup $K\le GL_2(F)$ that is open and compact as a set, and every $\varphi\colon M_{2\times 3}(F)\to GL_2(F)\to\mathbb C$ given by the closed formula $$\varphi(X)(g)=\mu_2(K)^{-1}\lambda_0(\det T)\,\|\det T\|\,\mathbf 1_{K}(s)\,\lambda_0(\det s)^{-1}\|\det s\|^{-1}\,\|\det g\|^{1/2}\,\lambda_1\!\big(\tfrac{\det g\,\det s}{N_{10}}\big)\lambda_2(N_{10})\,\|N_{10}\|^{-1}\,\Phi\!\big(\tfrac{N_{11}}{N_{10}},\tfrac{N_{12}}{N_{10}},\tfrac{Z_{00}Z_{12}-Z_{02}Z_{10}}{\det s}\big),$$ where $Z=XT$, $s$ is the first two columns of $Z$, $N=gZ$, the characters are extended by $0$ at $0$, and $\mathbf 1_K$ is the indicator of the image of $K$ in $M_2(F)$: the map $(X,g)\mapsto\varphi(X)(g)$ is measurable; $X\mapsto\varphi(X)$ is locally constant with compact support; $\varphi(X)(g)\neq 0$ forces $s\in K$; each $\varphi(X)$ is locally constant, invariant under left translation by $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(X)(\mathrm{diag}(a_0,a_1)g)=\lambda_1(a_0)\lambda_2(a_1)\sqrt{\|a_0\|/\|a_1\|}\,\varphi(X)(g)$, with $\varphi(X)(g)\neq 0$ implying $(gs)_{10}\neq 0$ and $\|(gs)_{11}\|\le R\|(gs)_{10}\|$; and if $K\subseteq U$ then $\varphi(X)(g)\neq 0$ implies $g_{10}\neq 0$ and $\|g_{11}\|\le R\|g_{10}\|$.
--
--   These are the local properties of the explicit Godement section attached to a vector $\Phi$, a triple of quasi-characters and a point $T\in GL_3(F)$: each slot vector is a vector in the principal series of $GL_2(F)$ attached to $(\lambda_1,\lambda_2)$, supported in the big cell and, as a function of the matrix variable, locally constant of compact support. They are used in the Rankin–Selberg construction for the cubic induction, being cited by [`LanglandsTunnell.CubicInduction.exists_finset_pureTensor_godementDatum`](thm.html#LanglandsTunnell.CubicInduction.exists_finset_pureTensor_godementDatum) and by the comparison of the Jacquet and Godement Whittaker functionals on a chamber.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_godementDatum_mem_principalSeries2_and_support.lean

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

theorem LanglandsTunnell.CubicInduction.godementDatum_mem_principalSeries2_and_support
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) := borel _
    ∃ (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) (R : ℝ), IsOpen U ∧ (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ U ∧
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

    Measurable (fun P : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) => φsec P.1 P.2) ∧
    IsLocallyConstant φsec ∧ HasCompactSupport φsec ∧
    (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), φsec X g ≠ 0 →
      (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j)) ∈ Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))) ∧

    (∀ X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ),
      φsec X ∈ principalSeries2 p ![lam 1, lam 2] ∧
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φsec X g ≠ 0 →
        ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 0 ≠ 0 ∧
        ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 1‖ ≤ R * ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 0‖) ∧

    ((K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ⊆ U →
      ∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), φsec X g ≠ 0 →
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ≠ 0 ∧ ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ≤ R * ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖) := by sorry
