-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_depth_bound
-- name    : OAI.ShortEgyptian.depth_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:23:55.626632+00:00
-- url     : https://prove2.me/theorems/4ce11117-9a66-4889-988b-c217fd73a92d
-- title:
--   The number of scale levels is $O(\log S)$
-- statement:
--   Let $d_X=204206$ be the fixed dimension constant of the construction; in the development $d_X=d_M+2$ with $d_M=(2\cdot1000+2)(100+2)=204204$. For real $S$ let $m(S)=\lfloor S/\log S\rfloor$, and define the *depth*
--
--   $$\operatorname{depth}(S)=\Bigl\lceil\frac{d_X\,S-m(S)}{m(S)/10000}\Bigr\rceil .$$
--
--   This is the number of steps of length $m(S)/10000$ needed to lower the exponent of the scale levels $\exp\bigl(d_XS-j\,m(S)/10000\bigr)$, $j=0,1,2,\dots$, from $d_XS$ down to $m(S)$.
--
--   **Theorem.** If $S>0$, $\log S\ge1$ and
--
--   $$\frac{S}{2\log S}\le m(S)\le S,$$
--
--   then
--
--   $$
--   \operatorname{depth}(S)\;\le\;3\cdot d_X\cdot 10000\cdot\log S .
--   $$
--
--   The depth is the number of scales at which Fourier-bad moduli have to be controlled simultaneously. The lemma shows that it grows only logarithmically in $S$. This is what makes a union bound over all scales affordable, namely $\operatorname{depth}(S)\,e^{-m(S)/250}<\frac12$ for large $S$.
--
--   **Formalization Note** $m(S)$ is `scaleM S` (a natural-number floor), $d_X$ is the irreducible constant `dimX`, and the depth uses the natural-number ceiling `⌈·⌉₊`, which is $0$ for negative arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ScaleGeometry.lean#L78-L92

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

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical Filter Topology

theorem OAI.ShortEgyptian.depth_bound (S : ℝ) (hS : 0 < S) (hlog : 1 ≤ Real.log S)
    (hm : S/(2*Real.log S) ≤ (scaleM S:ℝ)) (hmS : (scaleM S:ℝ) ≤ S) :
    (depth S:ℝ) ≤ (3*(dimX:ℝ)*10000)*Real.log S := by sorry
