-- Prove2me | Theorems.Thm_OAI_MatchingInterpolation_interpolation_matrix_domination
-- name    : OAI.MatchingInterpolation.interpolation_matrix_domination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:22:05.367976+00:00
-- url     : https://prove2.me/theorems/b4222613-1426-4210-b17f-2ff8a22553e3
-- title:
--   Loewner domination from entrywise polynomial approximation at five special points and a dilated grid
-- statement:
--   Let $R$ be a finite index set. All matrices are real $R\times R$ matrices, PSD means positive semidefinite, and $X\preceq Y$ is the Loewner order ($Y-X$ is PSD). Let $d\in\mathbb{N}$; $\mathcal P_d$ denotes the real vector space of functions $\mathbb{R}^3\to\mathbb{R}$ spanned by all products of at most $d$ coordinate functions $x\mapsto x_a$, $a\in\{0,1,2\}$ (repetitions allowed, the empty product being the constant $1$); these are exactly the polynomial functions of total degree at most $d$ in three variables.
--
--   **Interpolation weights.** For $k\in\{0,\dots,d\}$ let $\ell_k(\tau)=\prod_{j\in\{0,\dots,d\},\,j\neq k}\frac{\tau-j}{k-j}$ be the Lagrange basis polynomial of the nodes $0,1,\dots,d$, and for $g\in\{0,\dots,d\}^3$ and $v\in\mathbb{R}^3$ let $\Lambda_{g,v}(\tau)=\prod_{a=0}^{2}\ell_{g_a}(v_a\tau)$. With $\alpha=(0,2,0)$, $\beta=(0,0,2)$, $\sigma=(2,0,0)$ and $\pi=(-1,1,1)$ put $w_{d,L}(g)=\big(\Lambda_{g,\alpha}+\Lambda_{g,\beta}-\Lambda_{g,\sigma}-2\Lambda_{g,\pi}+\Lambda_{g,0}\big)(1/L)$, and let $W_{d,L}=\sum_{g\in\{0,\dots,d\}^3}|w_{d,L}(g)|$ be the weight mass. With the base point $o=(1,0,0)$, the five special points are $p_1=o$, $p_2=o+\pi=(0,1,1)$, $p_3=o+\sigma=(3,0,0)$, $p_4=o+\alpha=(1,2,0)$, $p_5=o+\beta=(1,0,2)$, and the scaled grid nodes are $z_g=o+Lg=(1+Lg_0,\,Lg_1,\,Lg_2)$ for $g\in\{0,\dots,d\}^3$.
--
--   **Theorem.** Let $B:\mathbb{R}^3\to\mathbb{R}^{R\times R}$ be such that $B(x)$ is PSD for every $x\in\mathbb{R}^3$, let $P_{uv}\in\mathcal P_d$ for $u,v\in R$, and let $L\neq0$ and $\eta\ge0$ be reals such that for all $u,v\in R$
--   $$\big|B(p_j)_{uv}-P_{uv}(p_j)\big|\le\eta\ \ (j=1,\dots,5),\qquad \big|B(z_g)_{uv}-P_{uv}(z_g)\big|\le\eta\ \ \big(g\in\{0,\dots,d\}^3\big).$$
--   Then there is a PSD matrix $E$ such that
--   1. $B(o+\alpha)+B(o+\beta)\preceq B(o+\sigma)+2B(o+\pi)+E$, and
--   2. for every real matrix $Q$ (not necessarily PSD) and all reals $m,k$ with $\operatorname{tr}Q\le m$ and $\operatorname{tr}\big(QB(z_g)\big)\le k$ for every $g$,
--   $$\operatorname{tr}(QE)\le W_{d,L}\,k+|R|\,\big(6+W_{d,L}\big)\,\eta\,m.$$
--
--   If every entry of $B$ were itself a polynomial in $\mathcal P_d$, the five-point interpolation identity would express $B(o+\alpha)+B(o+\beta)-B(o+\sigma)-2B(o+\pi)+B(o)$ exactly through the grid values $B(z_g)$. The theorem is the robust matrix version: under entrywise $\eta$-approximation one gets a Loewner inequality with an explicit PSD error $E$, and the size of $E$ tested against any $Q$ is controlled by the pairings of $Q$ with the grid values and by $\eta$. In the perfect matching argument $B$ is a cell-averaged factor matrix, the grid pairings are at most linear in $L$, and the weight mass is $O(L^{-2})$, which makes the error small.
--
--   **Formalization Note** The order is Mathlib's Loewner order on `Matrix R R ℝ` (scope `MatrixOrder`). The special points are `specialPoint j` for `j : Fin 5`, the nodes are `scaledNode L g`, and $W_{d,L}$ is `weightMass d L`. The function $B$ is defined, and assumed PSD, on all of $\mathbb{R}^3$, although only its values at the special points and the nodes enter.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/MatrixInterpolation.lean#L71-L125

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

open OAI OAI.MatchingInterpolation
universe u_1 u_2
open MatchingSmoothing Matrix PerfectMatchingPSD
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable
variable {R : Type u_2} [Fintype R] [DecidableEq R]

theorem OAI.MatchingInterpolation.interpolation_matrix_domination (d : ℕ)
    (B : Point → Matrix R R ℝ) (hB : ∀ x, (B x).PosSemidef)
    (P : R → R → Point → ℝ) (hP : ∀ u v, P u v ∈ lowDegree coord d)
    {L η : ℝ} (hL : L ≠ 0) (hη : 0 ≤ η)
    (hs : ∀ j u v, |B (specialPoint j) u v-P u v (specialPoint j)| ≤ η)
    (hg : ∀ g : GridIndex d, ∀ u v, |B (scaledNode L g) u v-P u v (scaledNode L g)| ≤ η) :
    ∃ E : Matrix R R ℝ, E.PosSemidef ∧
      B (origin+dirA)+B (origin+dirB) ≤ B (origin+dirStar)+(2:ℝ) • B (origin+dirP)+E ∧
      ∀ (Q : Matrix R R ℝ) (m k : ℝ), Q.trace ≤ m →
        (∀ g : GridIndex d, (Q*B (scaledNode L g)).trace ≤ k) →
        (Q*E).trace ≤ weightMass d L*k +
          (Fintype.card R : ℝ)*(6+weightMass d L)*η*m := by sorry
