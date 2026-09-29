-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_apply_row_localLevelOne_eq_zero_and_eq_apply_zero_of_isLocallyConstant_of_hasCompactSupport
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_apply_row_localLevelOne_eq_zero_and_eq_apply_zero_of_isLocallyConstant_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/605be369-c7b9-5a04-8fc4-2333365e68f0
-- title:
--   Uniform radial profile of a Schwartz–Bruhat function on bottom rows
-- statement:
--   Let $p$ be a nonzero prime ideal of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_p$ (written `p.adicCompletion ℚ`) and valuation ring `p.adicCompletionIntegers ℚ`. Let $\Phi_2 : \mathbb{Q}_p \times \mathbb{Q}_p \to \mathbb{C}$ be locally constant and of compact support, and let $\varpi$ be an element of the valuation ring whose image in $\mathbb{Q}_p$ is nonzero and has valuation $\exp(-1)$, i.e. a uniformiser. Then there exist integers $n_{\mathrm{lo}} \le n_{\mathrm{hi}}$, depending on $\Phi_2$ and $\varpi$ only, such that for every $k$ in the subgroup $\mathrm{localLevelOne}$ of $\mathrm{GL}_2(\mathbb{Q}_p)$ attached to the unit ideal $\top$ — that is, every $k$ whose image under the embedding [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of $\mathrm{GL}_2(\mathbb{Q}_p)$ into $\mathrm{GL}_2$ of the finite adele ring (the matrix of $k$ at $p$, the identity elsewhere) is such that both it and the corresponding matrix of $k^{-1}$ satisfy the predicate `IsLevelOneMatrix` for the ideal $\top$ — and for every $n \in \mathbb{Z}$, one has $\Phi_2(\varpi^n k_{10}, \varpi^n k_{11}) = 0$ whenever $n < n_{\mathrm{lo}}$, and $\Phi_2(\varpi^n k_{10}, \varpi^n k_{11}) = \Phi_2(0,0)$ whenever $n_{\mathrm{hi}} \le n$, where $(k_{10}, k_{11})$ is the second row of the matrix of $k$.
--
--   This is the elementary radial profile of a Schwartz–Bruhat function on $\mathbb{Q}_p^2$ restricted to the rays through the bottom rows of the level-one group: compact support forces vanishing for sufficiently negative $n$, and local constancy at the origin forces the value $\Phi_2(0,0)$ for sufficiently large $n$, with bounds uniform in $k$. It feeds the shellwise evaluation of the local $\mathrm{GL}_2 \times \mathrm{GL}_2$ Rankin–Selberg integral in the Iwasawa decomposition, being used in the two results on the rationality of `rsLocalIntegral22` for principal series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_apply_row_localLevelOne_eq_zero_and_eq_apply_zero_of_isLocallyConstant_of_hasCompactSupport.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_apply_row_localLevelOne_eq_zero_and_eq_apply_zero_of_isLocallyConstant_of_hasCompactSupport
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ∃ (nlo nhi : ℤ), nlo ≤ nhi ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ,
        (n < nlo →
          Φ₂ ((algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ n * ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0),
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ n * ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) = 0) ∧
        (nhi ≤ n →
          Φ₂ ((algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ n * ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0),
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ n * ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) = Φ₂ (0, 0)) := by sorry
