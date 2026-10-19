-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_nearly_perfect_bit_tests
-- name    : OAI.PerfectMatchingPSD.nearly_perfect_bit_tests
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:14:39.180271+00:00
-- url     : https://prove2.me/theorems/350ddb06-06b3-4e36-8f98-cb825616232b
-- title:
--   Dimension lower bound $r\ge2^{q-1}$ for states whose $q$ bits can all be read almost perfectly
-- statement:
--   Let $R$ be a finite index set with $r=|R|$ elements, and consider real $r\times r$ matrices indexed by $R$. Write $X\preceq Y$ for the Loewner order ($Y-X$ positive semidefinite). Let $q\in\mathbb{N}$ and suppose that:
--
--   1. for every bit string $y\in\{0,1\}^q$ there is a real density matrix $\rho_y$, i.e. $\rho_y$ is symmetric positive semidefinite with $\operatorname{tr}\rho_y=1$;
--   2. for every position $i\in\{0,\dots,q-1\}$ there are matrices $F_{i,0},F_{i,1}$ with $0\preceq F_{i,b}$ and $F_{i,0}+F_{i,1}\preceq I$, a two-outcome measurement for the $i$-th bit;
--   3. $\varepsilon\ge0$ satisfies $q\sqrt{\varepsilon}\le\tfrac14$;
--   4. every bit is decoded correctly with probability at least $1-\varepsilon$: $\operatorname{tr}(\rho_yF_{i,y_i})\ge1-\varepsilon$ for all $y$ and $i$.
--
--   **Theorem.** Under these hypotheses
--   $$\frac{2^q}{2}\le r.$$
--
--   So $2^q$ states of dimension $r$ from which each of the $q$ bits can be read off with error at most $\varepsilon$, by measurements that do not depend on the state, force $r\ge2^{q-1}$ as soon as $q\sqrt\varepsilon\le1/4$. In the PSD-rank lower bound for perfect matchings, a small PSD factorization is turned into such a family of states and measurements, and this theorem then forces the factorization size to be exponentially large in $q$.
--
--   **Formalization Note** Bit strings are functions `Fin q → Bool`, with `false` and `true` playing the roles of $0$ and $1$. The Loewner order is the `MatrixOrder` instance, so `0 ≤ F i b` means that $F_{i,b}$ is symmetric positive semidefinite. The conclusion is stated over the reals as `(2:ℝ)^q / 2 ≤ Fintype.card R`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/SequentialTests.lean#L139-L157

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

open OAI OAI.PerfectMatchingPSD
universe u_1 u_2
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {R : Type u_1} [Fintype R] [DecidableEq R]

theorem OAI.PerfectMatchingPSD.nearly_perfect_bit_tests {q : ℕ}
    (ρ : (Fin q → Bool) → Matrix R R ℝ) (F : Fin q → Bool → Matrix R R ℝ)
    (hρ : ∀ y, (ρ y).PosSemidef) (htρ : ∀ y, (ρ y).trace = 1)
    (hF : ∀ i b, 0 ≤ F i b) (hpair : ∀ i, F i false + F i true ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : (q:ℝ)*Real.sqrt ε ≤ 1/4)
    (hsuccess : ∀ y i, 1-ε ≤ (ρ y * F i (y i)).trace) :
    (2:ℝ)^q / 2 ≤ Fintype.card R := by sorry
