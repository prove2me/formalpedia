-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_terminal_interval
-- name    : OAI.ShortEgyptian.terminal_interval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:29:12.584569+00:00
-- url     : https://prove2.me/theorems/90356cb3-03bc-4432-9c95-f9f1134af70c
-- title:
--   Logarithmic window for the terminal numerators $S^{100000}<u\le e^{m(S)}$
-- statement:
--   Fix the absolute constants $D_M=2002\cdot102=204204$, $D_X=D_M+2=204206$ and $D_C=4D_X=816824$, and for $r\in\mathbb{N}$ let $P(r)=2^r(2r+4)$ and $K(r)=(18\cdot3^{r+3})^4\,((r+2)!)^2\,2^{2r}$. For a real number $S$ put $m(S)=\lfloor S/\log S\rfloor$ and
--
--   $$\operatorname{depth}(S)=\Big\lceil\frac{D_XS-m(S)}{m(S)/10000}\Big\rceil .$$
--
--   A real number $S$ is an *admissible scale* if (i) $S\ge2$; (ii) $\log S\ge100$; (iii) $100001\log S\le S$; (iv) $10^6\log S\le m(S)$; (v) $P(3D_C)\le\log S$; (vi) $K(3D_C)\,32^{P(3D_C)}\le e^{S/4}$; (vii) $\operatorname{depth}(S)\,e^{-m(S)/250}<\tfrac12$. All seven conditions hold for every sufficiently large $S$.
--
--   **Theorem.** Let $S$ be an admissible scale and let $u$ be a natural number with $\lfloor S^{100000}\rfloor+1\le u\le\lfloor e^{m(S)}\rfloor$. Then
--
--   $$u\ge3,\qquad 100000\log S\le\log u,\qquad \log u\le m(S).$$
--
--   The integers in this range are the moduli treated in the terminal stage of the construction of short Egyptian fraction expansions. The lemma records the side conditions (at least $3$, and $\log u$ between $100000\log S$ and $m(S)$) that the probabilistic choice of the sampled prime lists requires of every terminal modulus.
--
--   **Formalization Note** Admissibility is the structure `ListScale S`; $m(S)$ is `scaleM S`, $D_M,D_X,D_C$ are `dimM`, `dimX`, `dimC`, and $P,K$ are `reciprocalPower`, `reciprocalConstantNat`. The range of $u$ is `Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S)⌋₊`, with natural-number floors and ceilings throughout.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ResidueSystem.lean#L32-L46

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

open OAI OAI.ShortEgyptian
universe uA
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.terminal_interval (S : ℝ) (h : ListScale S) (u : ℕ)
    (hu : u ∈ Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S:ℝ)⌋₊) :
    3 ≤ u ∧ 100000*Real.log S ≤ Real.log u ∧ Real.log u ≤ (scaleM S:ℝ) := by sorry
