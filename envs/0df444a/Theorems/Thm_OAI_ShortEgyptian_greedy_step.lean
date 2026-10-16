-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_greedy_step
-- name    : OAI.ShortEgyptian.greedy_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:48:35.65703+00:00
-- url     : https://prove2.me/theorems/bd7e44bd-ff6e-4924-bbba-d34a2a93e6a1
-- title:
--   One step of the greedy Egyptian fraction algorithm
-- statement:
--   Let $A,C$ be natural numbers with $0<A<C$, and put $z=\lceil C/A\rceil$ and $r=Az-C$. The greedy step writes
--
--   $$
--   \frac AC=\frac1z+\frac{r}{Cz},
--   $$
--
--   and more precisely the following hold:
--
--   1. $2\le z\le C$;
--   2. $r<A$;
--   3. $A/C=1/z+r/(Cz)$ (the identity above);
--   4. $r/(Cz)\le(A/C)^2$;
--   5. $r/(Cz)\le\frac12$.
--
--   Here $1/z$ is the largest unit fraction not exceeding $A/C$, so this is one step of the greedy (Fibonacci–Sylvester) algorithm. The new numerator $r$ is strictly smaller than $A$, the new denominator $Cz$ is at most $C^2$, and the remainder is at most the square of the original fraction. Iterating, the remainders decay doubly exponentially, which is the basis of the greedy preparation stage.
--
--   **Formalization Note** $z$ and $r$ are `quotient C A` (the natural-number ceiling of the rational $C/A$) and `residue C A z` (defined with truncated subtraction, which is harmless since $Az\ge C$). The identity (3) is stated in $\mathbb Q$, and the inequalities (4) and (5) in $\mathbb R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean#L9-L55

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

theorem OAI.ShortEgyptian.greedy_step (A C : ℕ) (hA : 0 < A) (hAC : A < C) :
    let z := quotient C A
    let r := residue C A z
    2 ≤ z ∧ z ≤ C ∧ r < A ∧
      (A:ℚ)/C = 1/(z:ℚ)+(r:ℚ)/(C*z) ∧
      (r:ℝ)/(C*z) ≤ ((A:ℝ)/C)^2 ∧ (r:ℝ)/(C*z) ≤ 1/2 := by sorry
