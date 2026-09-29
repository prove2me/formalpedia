-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_pureTensor_godementDatum
-- name    : LanglandsTunnell.CubicInduction.exists_finset_pureTensor_godementDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/da7b7fbf-9ec6-5b54-9b24-6a9225962b73
-- title:
--   Finite pure-tensor decomposition of the local Godement datum
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the completion of $\mathbb{Q}$ at $p$, let $\lambda_0,\lambda_1,\lambda_2 : F^\times \to \mathbb{C}^\times$ be locally constant characters, let $\Phi : F^3 \to \mathbb{C}$ be locally constant with compact support, and let $T \in GL_3(F)$. All spaces carry their Borel structures. The assertion is: for every Haar measure $\mu_2$ on $GL_2(F)$, every subgroup $K \le GL_2(F)$ whose underlying set is open and compact, and every function $\varphi^{\mathrm{sec}} : M_{2\times 3}(F) \times GL_2(F) \to \mathbb{C}$ given by the explicit formula
--   $$\varphi^{\mathrm{sec}}(X,g) = \mu_2(K)^{-1}\,\lambda_0(\det T)\,|\det T|\; \mathbf{1}_{K}(s)\;\lambda_0(\det s)^{-1}\,\|\det s\|^{-1}\,|\det g|^{1/2}\,\lambda_1\!\left(\tfrac{\det g \cdot \det s}{N_{10}}\right)\lambda_2(N_{10})\,\|N_{10}\|^{-1}\,\Phi\!\left(\tfrac{N_{11}}{N_{10}},\tfrac{N_{12}}{N_{10}},\tfrac{Z_{00}Z_{12}-Z_{02}Z_{10}}{\det s}\right),$$
--   where $Z = XT$, $s$ is the left $2\times 2$ block of $Z$, $N = gZ$, $\mathbf{1}_K$ is the indicator of the image of $K$ in $M_2(F)$, $|\cdot|$ denotes the module $\mathrm{modulus}$ given by the distributive Haar character (and $0$ at $0$), and each $\lambda_i$ is extended by $0$ at $0$ via `charExt` — there exist $m \in \mathbb{N}$ and families $\phi_{1,i} : M_2(F) \to \mathbb{C}$, $\phi_{2,i} : F \times F \to \mathbb{C}$, $\varphi_i : GL_2(F) \to \mathbb{C}$ ($i < m$) such that each $\phi_{1,i}$ and each $\phi_{2,i}$ is locally constant with compact support; each $\varphi_i$ lies in `principalSeries2 p ![lam 1, lam 2]`, i.e. is locally constant, left invariant under the upper unipotent subgroup, and satisfies $\varphi_i(\mathrm{diag}(a_0,a_1)g) = \lambda_1(a_0)\lambda_2(a_1)\sqrt{\|a_0\|/\|a_1\|}\,\varphi_i(g)$; for each $i$ there is $s_i \in K$ with $\varphi_i(g) \ne 0 \Rightarrow (g s_i)_{10} \ne 0$; one has the pure-tensor identity $\varphi^{\mathrm{sec}}(X,g) = \sum_{i<m} \phi_{1,i}(X')\,\phi_{2,i}(X_{02},X_{12})\,\varphi_i(g)$, where $X'$ is the left $2\times 2$ block of $X$; and each summand is dominated in absolute value by $\varphi^{\mathrm{sec}}(X,g)$, for all $i$, $X$ and $g$.
--
--   This is the local pure-tensor (finite sum of factorisable vectors) decomposition of the explicit $GL_3$ Godement section in the non-archimedean Rankin–Selberg theory of Jacquet, Piatetski-Shapiro and Shalika, with the extra feature that each $GL_2$ factor lies in the principal series attached to $(\lambda_1,\lambda_2)$, is supported where a translate has nonvanishing $(1,0)$ entry, and that the decomposition is norm-dominated term by term. It is used in the cubic-induction comparison of Whittaker functions, being cited by [`LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber`](thm.html#LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber), where the Whittaker transform is applied slot by slot to each factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_finset_pureTensor_godementDatum.lean

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

theorem LanglandsTunnell.CubicInduction.exists_finset_pureTensor_godementDatum
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
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
    ∃ (m : ℕ) (φ₁ : Fin m → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
        (φ₂ : Fin m → (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
        (φ : Fin m → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ i, IsLocallyConstant (φ₁ i) ∧ HasCompactSupport (φ₁ i)) ∧
      (∀ i, IsLocallyConstant (φ₂ i) ∧ HasCompactSupport (φ₂ i)) ∧
      (∀ i, φ i ∈ principalSeries2 p ![lam 1, lam 2] ∧
        ∃ s ∈ K, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φ i g ≠ 0 →
          ((g * s : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ≠ 0) ∧
      (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        φsec X g = ∑ i, φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i g) ∧
      (∀ (i : Fin m) (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ‖φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i g‖ ≤ ‖φsec X g‖) := by sorry
