-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_holder_density
-- name    : OAI.ShortEgyptian.holder_density
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:37:20.207989+00:00
-- url     : https://prove2.me/theorems/1795c739-7cd2-46d8-b0a7-8ae069ff0a1e
-- title:
--   Hölder bound for a sum in terms of an $r$-th moment bound and a density
-- statement:
--   Let $H$ be a finite set, $f$ a real-valued function with $f(i)\ge0$ for every $i\in H$, $r\ge2$ an integer, and $Y,E$ real numbers with $Y>0$.
--
--   **Theorem.** If
--
--   $$\sum_{i\in H}f(i)^r\le Y\,e^{E},$$
--
--   then
--
--   $$\sum_{i\in H}f(i)\le Y\,e^{E/r}\Big(\frac{|H|}{Y}\Big)^{1-1/r}.$$
--
--   The bound converts a control of the $r$-th moment of $f$ over $H$ into a control of its first moment, with a gain given by the power $1-1/r$ of the relative size (density) $|H|/Y$. In the construction of short Egyptian fraction expansions it is applied with $Y$ a level of the descent and $H$ the exceptional set at that level, to bound sums of divisor-counting functions over the exceptional set in terms of its density.
--
--   **Formalization Note** $H$ is a `Finset` of an arbitrary type, $f$ is defined on the whole type but is assumed nonnegative only on $H$, and the power with exponent $1-1/r$ is the real power `Real.rpow` of the nonnegative number $|H|/Y$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/Holder.lean#L23-L40

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

open OAI OAI.ShortEgyptian
universe uι
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.holder_density {ι : Type uι} (H : Finset ι) (f : ι → ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hf : ∀ i ∈ H, 0 ≤ f i) (Y E : ℝ) (hY : 0 < Y)
    (hm : ∑ i ∈ H, (f i)^r ≤ Y*Real.exp E) :
    ∑ i ∈ H, f i ≤ Y*Real.exp (E/(r:ℝ))*((H.card:ℝ)/Y)^(1-1/(r:ℝ)) := by sorry
