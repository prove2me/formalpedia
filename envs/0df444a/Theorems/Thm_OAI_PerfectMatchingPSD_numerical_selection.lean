-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_numerical_selection
-- name    : OAI.PerfectMatchingPSD.numerical_selection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:33:18.023002+00:00
-- url     : https://prove2.me/theorems/5035e76f-129f-42f9-a201-b11ab974e7a1
-- title:
--   Numerical parameter inequality feeding the conditional cell lower bound
-- statement:
--   Let $p,d,t,r,n,T\in\mathbb{N}$ and let $b=4(d+1)t^4$ (the block size). Assume $t\ge2$, $r\ge1$, $n\le t^6$, $T\le t$ and $r\le n^p$.
--
--   **Theorem.** Under these assumptions
--   $$\frac{t\,r^4\,T}{\big(2(3b+1)\big)^{20(p+1)}}\le\Big(\frac{1}{r\,(n+1)\cdot2t^4}\Big)^2.$$
--
--   This is the first numerical hypothesis of the conditional cell lower bound for $K=10(p+1)$ (so $2K=20(p+1)$), with $q=t$ cells, block size $s=b$, $l=t^4$ (so $2l=2t^4$), trace bound $m=n+1$, and $T$ standing for the number $5+(d+1)^3$ of sample points. In the main argument $r$ is the PSD rank on $n$ vertices, the assumption $r\le n^p$ is the hypothesis to be refuted, and $t$ is chosen according to $n$ so that $n\le t^6$.
--
--   **Formalization Note** All quantities are cast to $\mathbb{R}$; $n^p$ is the power of the real number $n$ with natural exponent $p$, and $b$ is `blockSize d t`. The parameter $d$ enters only through $b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/NumericalBounds.lean#L29-L66

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Padding
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Parameters

open OAI OAI.PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix
open scoped BigOperators MatrixOrder

theorem OAI.PerfectMatchingPSD.numerical_selection (p d t r n T : ℕ) (ht : 2 ≤ t) (hr : 0 < r)
    (hn : n ≤ t^6) (hT : T ≤ t) (hrn : (r:ℝ) ≤ (n:ℝ)^p) :
    (t:ℝ)*r^4*T*((2*(3*(blockSize d t:ℝ)+1))^(2*(10*(p+1))))⁻¹ ≤
      (1/((r:ℝ)*((n:ℝ)+1)*(2*(t:ℝ)^4)))^2 := by sorry
