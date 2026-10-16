-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_random_lengths
-- name    : OAI.ShortEgyptian.random_lengths
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:03:20.437131+00:00
-- url     : https://prove2.me/theorems/098e5337-7d6a-45e5-95fb-e93d68ff75e2
-- title:
--   Size bounds for the parameters $\lfloor S/\log S\rfloor$ and $\lfloor 3V/(400\log S)\rfloor$
-- statement:
--   Let $S$ and $V$ be real numbers with $\log S\ge1$, $200\log S\le S$, $100000\log S\le V$ and $V\le S$, where $\log$ is the natural logarithm, and define the natural numbers
--   $$m=\Bigl\lfloor\frac{S}{\log S}\Bigr\rfloor,\qquad s=\Bigl\lfloor\frac{3V}{400\log S}\Bigr\rfloor .$$
--   Then all of the following hold:
--
--   $$
--   \begin{gathered}
--   \frac{S}{2\log S}\le m\le S,\qquad \frac{V}{140\log S}\le s\le\frac{3V}{400\log S},\\
--   8s\le m,\qquad s\le S,\qquad 100\le\min(m,V).
--   \end{gathered}
--   $$
--
--   These are the parameter choices for the random-prime model: $m$ is the number of coordinates, $V$ plays the role of $\log u$ for the modulus $u$, and $s$ is the common size of the two disjoint coordinate sets on which fresh primes are exposed. The inequalities guarantee that $s$ is of order $V/\log S$, that $4\cdot(2s)\le m$, and that the final error exponent $\min(m,V)$ is at least $100$.
--
--   **Formalization Note** The floors are natural-number floors `⌊·⌋₊`; $m$ and $s$ are introduced by `let`, and the conclusion is a conjunction of the seven inequalities, with $8s\le m$ stated in $\mathbb N$ and the others in $\mathbb R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/RandomBounds.lean#L13-L53

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

open OAI OAI.ShortEgyptian
universe uJ uA
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.ShortEgyptian.random_lengths (S V : ℝ) (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (hV : 100000*Real.log S ≤ V) (hVS : V ≤ S) :
    let m := ⌊S/Real.log S⌋₊
    let s := ⌊3*V/(400*Real.log S)⌋₊
    S/(2*Real.log S) ≤ (m:ℝ) ∧ (m:ℝ) ≤ S ∧
      V/(140*Real.log S) ≤ (s:ℝ) ∧ (s:ℝ) ≤ 3*V/(400*Real.log S) ∧
      8*s ≤ m ∧ (s:ℝ) ≤ S ∧ 100 ≤ min (m:ℝ) V := by sorry
