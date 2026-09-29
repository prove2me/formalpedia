-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge
-- name    : LanglandsTunnell.CubicInduction.exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/d3998681-4f5c-5526-b3a2-53dbad305e5a
-- title:
--   Twisted translated Jacquet–Whittaker function: admissible, unitary central, gauged
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, write $\mathbb{Q}_p$ for the completion at $p$, let $\lambda_0,\lambda_1,\lambda_2\colon \mathbb{Q}_p^{\times}\to\mathbb{C}^{\times}$ be locally constant group homomorphisms, let $\Phi\colon \mathbb{Q}_p^{3}\to\mathbb{C}$ be locally constant with compact support, let $x,y,z\in\mathbb{Q}_p$, and let $W_3\colon \mathrm{GL}_3(\mathbb{Q}_p)\to\mathbb{C}$ be the function $h\mapsto \mathrm{jacquetWhittaker3}\,(\lambda,\Phi)$ evaluated at $\mathrm{diag}(1,-1,1)\,h\,u(x,y,z)\,w$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$ above the diagonal, $w$ is the antidiagonal permutation matrix, and $\mathrm{jacquetWhittaker3}$ at $g$ is the Jacquet value `jacquetValue` of the right translate by $g$ of the cell section attached to $(\lambda,\Phi)$. Then there exist a real number $a$, a group homomorphism $\omega_3\colon \mathbb{Q}_p^{\times}\to\mathbb{C}^{\times}$ and a function $W'\colon \mathrm{GL}_3(\mathbb{Q}_p)\to\mathbb{C}$ with the following properties. First, $W'(h)=|\det h|^{a}W_3(h)$ for all $h$, the absolute value being the module `modulus` of the determinant, raised to the complex power $a$. Second, $W'$ transforms under the unipotent radical by the inverse of the standard local additive character: $W'(u(x',y',z')g)=\psi_p^{-1}(x'+y')\,W'(g)$ for all $x',y',z'$ and $g$. Third, there is an open subgroup $U$ of $\mathrm{GL}_3(\mathbb{Q}_p)$ with $W'(gk)=W'(g)$ for all $k\in U$, $g$. Fourth, $W'(t\cdot h)=\omega_3(t)W'(h)$ for scalar matrices $t\in \mathbb{Q}_p^{\times}$, and $|\omega_3(t)|=1$ for all $t$. Fifth, for every open subgroup $U$ there is a finite set $B$ of functions such that every element of the span of the right translates of $W'$ which is right $U$-invariant lies in the $\mathbb{C}$-span of $B$. Sixth, there are $B\in\mathbb{R}$, $t\in\mathbb{N}$, $C\in\mathbb{R}$ such that, writing $\rho_1(h)=\|\det h\|\cdot r(h)/m(h)^2$ and $\rho_2(h)=m(h)/r(h)^2$ with $r(h)$ the maximum of the norms of the three entries of the bottom row of $h$ and $m(h)$ the maximum of the norms of the three $2\times 2$ minors formed from the last two rows, one has $W'(h)=0$ unless both $\rho_1(h)\le B$ and $\rho_2(h)\le B$, and $\|W'(h)\|\le C/(\rho_1(h)\rho_2(h))^{t}$ whenever both inequalities hold.
--
--   This packages the Jacquet–Whittaker function of a principal series of $\mathrm{GL}_3(\mathbb{Q}_p)$, translated on both sides and twisted by a real power of the determinant, into a Whittaker function for the inverse standard character that is smooth, has unitary central character, generates an admissible module of right translates, and satisfies a gauge estimate in the two simple-root sizes. It is the input used by the local Rankin–Selberg integral statements for such translated Jacquet–Whittaker functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge.lean

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

theorem LanglandsTunnell.CubicInduction.exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (x y z : p.adicCompletion ℚ)
    (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ = fun h => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p)))
    :
    ∃ (a : ℝ) (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (W' : LocalGL3 p → ℂ),
      (∀ h : LocalGL3 p, W' h =
        (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (a : ℂ)) *
          W₃ h) ∧
      IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W' ∧
      (∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 p, W' (g * k) = W' g) ∧
      (∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
        W' (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W' h) ∧
      (∀ t : (p.adicCompletion ℚ)ˣ, ‖((ω₃ t : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
        ∃ B : Finset (LocalGL3 p → ℂ), ∀ F ∈ gl3CyclicSubspace W',
          (∀ k ∈ Uv, ∀ g : LocalGL3 p, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ))) ∧
      (∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
        (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W' h = 0) ∧
        (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
          ‖W' h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) := by sorry
