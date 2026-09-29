-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_integral_psiLocal_cellSectionOf
-- name    : LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_integral_psiLocal_cellSectionOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/8daabf2c-fa77-5eaf-95f7-45419463c9bc
-- title:
--   Jacquet–Whittaker function at diag(1,-1,1)Y as a ψ-integral
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ and write $F = \mathbb{Q}_p$ for the completion $p.adicCompletion\ \mathbb{Q}$, equipped with its Borel $\sigma$-algebra `localBorel`. Let $\lambda = (\lambda_0,\lambda_1,\lambda_2)$ be a triple of monoid homomorphisms $F^\times \to \mathbb{C}^\times$, each locally constant, and let $\sigma : \mathrm{Fin}\,3 \to \mathbb{R}$ satisfy $|\lambda_i(a)| = \|a\|^{\sigma_i}$ for all $i$ and all $a \in F^\times$, with $\sigma_2 < \sigma_1 < \sigma_0$. Let $\Phi : F^3 \to \mathbb{C}$ be locally constant with compact support, and let $Y \in \mathrm{GL}_3(F)$. Write $f_{\lambda,\Phi} =$ `cellSectionOf p lam Φ` for the function on $\mathrm{GL}_3(F)$ supported on the big cell $\{g : c(g) \neq 0,\ m(g) \neq 0\}$ (non-vanishing of the corner entry and of the lower $2\times 2$ minor) and given there by `cellValue` times $\Phi$ of `cellRatio`, and let $w_0 =$ `antidiagonal3 p`, $n(x,y,z) =$ `upperUnipotent3 x y z`, $d =$ `diagonal3 p ![1,-1,1]`. Then two things hold: first, $(x,y,z) \mapsto f_{\lambda,\Phi}(w_0\, n(x,y,z)\, Y)$ is integrable for the measure `jacquetHaar3 p`, the triple product of the self-dual Haar measure on $F$; second, the Jacquet–Whittaker function `jacquetWhittaker3 p lam Φ` (the truncated Jacquet value of the right translate of $f_{\lambda,\Phi}$) evaluated at $d\,Y$ equals $\lambda_1(-1)$ times $\int \psi_p(x+y)\, f_{\lambda,\Phi}(w_0\, n(x,y,z)\, Y)$, with $\psi_p$ the standard local additive character `psiLocal`.
--
--   This is the Jacquet integral formula for the Whittaker function of a $\mathrm{GL}_3$ principal-series cell section, evaluated along the twist by $\mathrm{diag}(1,-1,1)$, so that the kernel appearing is $\psi_p(x+y)$ rather than its inverse; thus $Y \mapsto W_{\lambda,\Phi}(dY)$ is a Whittaker function for the opposite additive character. It feeds the chamber statement `jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber`, from which the generic unfolding of the Rankin–Selberg integral proceeds.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_integral_psiLocal_cellSectionOf.lean

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

theorem LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_integral_psiLocal_cellSectionOf
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ), ‖((lam i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (Y : LocalGL3 p) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    Integrable (fun q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ =>
        cellSectionOf p lam Φ (antidiagonal3 p * upperUnipotent3 q.1 q.2.1 q.2.2 * Y)) (jacquetHaar3 p) ∧
    jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * Y) =
      ((lam 1 (-1) : ℂˣ) : ℂ) *
        ∫ q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ,
          NumberField.StandardAddChar.psiLocal ℚ p (q.1 + q.2.1) *
            cellSectionOf p lam Φ (antidiagonal3 p * upperUnipotent3 q.1 q.2.1 q.2.2 * Y) ∂(jacquetHaar3 p) := by sorry
