-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_domination_decoder
-- name    : OAI.PerfectMatchingPSD.domination_decoder
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:24:30.0097+00:00
-- url     : https://prove2.me/theorems/e203a399-f7ef-4478-9128-39f105ab4dd8
-- title:
--   Domination decoder: exact bit pairings under a PSD domination force matrix size at least $2^{q-1}$
-- statement:
--   Let $R$ be a finite index set and $q\in\mathbb{N}$. All matrices are real $R\times R$ matrices, PSD means positive semidefinite, $X\preceq Y$ means that $Y-X$ is PSD, and bits are written $0,1$. Suppose that we are given PSD matrices $Q_y$ for every bit string $y\in\{0,1\}^q$, $T_{i,b}$ for $i\in\{1,\dots,q\}$ and $b\in\{0,1\}$, $P_i$ and $E_i$ for $i\in\{1,\dots,q\}$, and $S$, such that for all $y$ and $i$
--   $$T_{i,0}+T_{i,1}\preceq S+2P_i+E_i,\qquad\operatorname{tr}(Q_yP_i)=0,\qquad\operatorname{tr}(Q_yS)=2,\qquad\operatorname{tr}(Q_yT_{i,y_i})=2.$$
--   Let $\delta>0$ and $m,e\in\mathbb{R}$ be such that $\operatorname{tr}Q_y\le m$ and $\operatorname{tr}(Q_yE_i)\le e$ for all $y$ and $i$, and put $\varepsilon=qe+\delta m$.
--
--   **Theorem.** If $\varepsilon\ge0$ and $q\sqrt{\varepsilon}\le\frac14$, then
--   $$|R|\ge\frac{2^q}{2}.$$
--
--   One may read $Q_y$ as an unnormalised state encoding the bit string $y$ and $(T_{i,0},T_{i,1})$ as a two-outcome test for the $i$-th bit that gives the correct answer with pairing exactly $2$. The domination hypothesis bounds both outcomes together by a common matrix $S$ plus error terms, of which $P_i$ is invisible to every $Q_y$ and $E_i$ is small against every $Q_y$. The conclusion is that the matrix size is exponential in the number of encoded bits. In the perfect matching argument the matrices are cell averages of the factors of a PSD factorization of order $r=|R|$, which turns this into a lower bound on $r$.
--
--   **Formalization Note** Bits are `Bool` with $0$ = `false` and $1$ = `true`, the order is Mathlib's Loewner order (scope `MatrixOrder`), and the conclusion is the real inequality `(2:ℝ)^q/2 ≤ Fintype.card R`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/DominationDecoder.lean#L12-L62

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

open OAI OAI.PerfectMatchingPSD
universe u_1
open Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

theorem OAI.PerfectMatchingPSD.domination_decoder {R : Type u_1} [Fintype R] [DecidableEq R] {q : ℕ}
    (Q : (Fin q → Bool) → Matrix R R ℝ)
    (T : Fin q → Bool → Matrix R R ℝ) (P E : Fin q → Matrix R R ℝ)
    (S : Matrix R R ℝ)
    (hQ : ∀ y, (Q y).PosSemidef) (hT : ∀ i b, (T i b).PosSemidef)
    (hP : ∀ i, (P i).PosSemidef) (hE : ∀ i, (E i).PosSemidef) (hS : S.PosSemidef)
    (hdom : ∀ i, T i false + T i true ≤ S+(2:ℝ) • P i+E i)
    (hzero : ∀ y i, (Q y*P i).trace=0) (hstar : ∀ y, (Q y*S).trace=2)
    (hbit : ∀ y i, (Q y*T i (y i)).trace=2)
    {m e δ : ℝ} (hδ : 0 < δ) (hm : ∀ y, (Q y).trace ≤ m)
    (he : ∀ y i, (Q y*E i).trace ≤ e)
    (hε : 0 ≤ (q:ℝ)*e+δ*m)
    (hsmall : (q:ℝ)*Real.sqrt ((q:ℝ)*e+δ*m) ≤ 1/4) :
    (2:ℝ)^q/2 ≤ Fintype.card R := by sorry
