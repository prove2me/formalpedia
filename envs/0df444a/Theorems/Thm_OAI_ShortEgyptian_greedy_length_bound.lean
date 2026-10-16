-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_greedy_length_bound
-- name    : OAI.ShortEgyptian.greedy_length_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:52:29.193186+00:00
-- url     : https://prove2.me/theorems/5f5a91d6-fb0c-4bb4-9a48-d2487fedf14e
-- title:
--   Explicit $O(\log S)$ bound on the number of greedy preparation steps
-- statement:
--   Let $D_C=816824$ be the fixed integer constant of this construction (it is defined as $D_C=4(D_M+2)$ with $D_M=2002\cdot 102$). For a real number $S$ define the number of greedy steps and the greedy constant by
--
--   $$
--   k(S)=\left\lceil\frac{\log\bigl(D_C S/\log 2\bigr)}{\log 2}\right\rceil,\qquad K_{\mathrm{gr}}=\frac{D_C}{(\log 2)^2}+\frac1{\log 2}+2,
--   $$
--
--   where the ceiling is taken in $\mathbb{N}$ (negative values are rounded up to $0$).
--
--   **Theorem.** For every real number $S$ with $S\ge 1$ and $\log S\ge 1$ (that is, $S\ge e$),
--
--   $$
--   k(S)+1\le K_{\mathrm{gr}}\,\log S .
--   $$
--
--   The step count $k(S)$ is chosen so that $2^{2^{k(S)}}\ge e^{D_C S}$, which is what the greedy preparation of a fraction with denominator $b=e^S$ needs to reach a remainder with denominator in $[e^{D_C S},e^{2D_C S})$. The lemma shows that this phase contributes at most $K_{\mathrm{gr}}\log S=K_{\mathrm{gr}}\log\log b$ unit fractions, with an explicit constant.
--
--   **Formalization Note** In Lean, $k(S)$ is `greedySteps S` (using the natural-number ceiling `Nat.ceil`), $K_{\mathrm{gr}}$ is `greedyConstant`, and $D_C$ is the irreducible constant `dimC`. Because Lean's `Real.log` satisfies $\log x=\log|x|$, the hypothesis $S\ge1$ is stated separately from $\log S\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean#L173-L201

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq

theorem OAI.ShortEgyptian.greedy_length_bound (S : ℝ) (hS : 1≤S) (hlog : 1≤Real.log S) :
    ((greedySteps S+1:ℕ):ℝ) ≤ greedyConstant*Real.log S := by sorry
