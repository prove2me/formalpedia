-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay
-- name    : LanglandsTunnell.CubicInduction.godementInner3_mulShift_polyGauss3_continuousOn_and_decay
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/3baca650-7e6f-5268-a6fd-16b789529b19
-- title:
--   Continuity and decay of the Godement inner integral
-- statement:
--   Let $a$ be a nonzero rational number and let `psiInf` be an additive character of the infinite adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$ which satisfies $\mathrm{psiInf}(x) = \mathrm{psiArch}(a x)$ for all $x$, where `psiArch` is the standard archimedean character, given at each infinite place by $x \mapsto \exp(2\pi i x)$ through the real embedding of the completion and multiplied over the infinite places. Let $S : M_{2\times 3}(\mathbb{R}) \to \mathbb{C}$ lie in `polyGauss3`, i.e. $S(M) = P\big((M_{ib})_{i,b}\big)\exp\big(-\pi\sum_{i,b} M_{ib}^2\big)$ for some polynomial $P$ in the six matrix entries with complex coefficients. For $y \in \mathbb{R}$ and $e \in M_2(\mathbb{R})$ write $G(y,e) = \int_{\mathbb{R}^2} S\big([\,e \mid e v\,]\big)\,\mathrm{psiInf}\big(\iota(y)\,\iota(-v_1)\big)\,dv$, the value of `godementInner3` for the character $\mathrm{psiInf}$ shifted by $\iota(y)$, at the pair $(e, 1)$, where $\iota(r)$ denotes the infinite adele with entry $r$ at each infinite place and $[\,e \mid e v\,]$ is the $2\times 3$ matrix whose first two columns are those of $e$ and whose third column is $ev$. The theorem asserts two things. First, $(y,e) \mapsto G(y,e)$ is continuous on $\{(y,e) : \det e \neq 0\}$. Second, for every $N \in \mathbb{N}$ there are $C \geq 0$ and $A \in \mathbb{N}$ such that for all $e \in M_2(\mathbb{R})$ with $\det e \neq 0$ and all $y \in \mathbb{R}$,
--   $$\|G(y,e)\| \le C\,|\det e|^{-1}\,\exp\Big(-\pi\sum_{i,j} e_{ij}^2\Big)\,\Big(1+\sum_{i,j} e_{ij}^2\Big)^{A}\Big(1 + y^2\sum_i \big((e^{-1})_{1i}\big)^2\Big)^{-N},$$
--   the sum $\sum_i ((e^{-1})_{1i})^2$ being the squared Euclidean length of the second row of $e^{-1}$.
--
--   This is the archimedean estimate for the inner Godement integral attached to a polynomial-times-Gaussian section: continuity away from the singular locus together with decay that is Gaussian in $e$ and of arbitrary polynomial order in $y\,\|{}^t e^{-1}(0,1)\|$. It is used by [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3) to dominate the integrand obtained after unfolding the Rankin–Selberg torus-pair integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.godementInner3_mulShift_polyGauss3_continuousOn_and_decay
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) :
    ContinuousOn
        (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
          godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal p.1)) S p.2 1)
        {p | p.2.det ≠ 0} ∧
      ∀ N : ℕ, ∃ C : ℝ, ∃ A : ℕ, 0 ≤ C ∧
        ∀ (e : Matrix (Fin 2) (Fin 2) ℝ) (y : ℝ), e.det ≠ 0 →
          ‖godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S e 1‖ ≤
            C * |e.det|⁻¹ * Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2)) * (1 + ∑ i, ∑ j, e i j ^ 2) ^ A *
              ((1 + y ^ 2 * ∑ i, (e⁻¹ 1 i) ^ 2) ^ N)⁻¹ := by sorry
