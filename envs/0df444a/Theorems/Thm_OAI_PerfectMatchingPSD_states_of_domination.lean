-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_states_of_domination
-- name    : OAI.PerfectMatchingPSD.states_of_domination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:16:37.059564+00:00
-- url     : https://prove2.me/theorems/4882ce3b-6fb4-4f32-9823-551e8df50b08
-- title:
--   From PSD tests dominated by a positive definite matrix to states and two-outcome measurements
-- statement:
--   Let $R$ be a finite index set and consider real square matrices indexed by $R$. Write $X\preceq Y$ for the Loewner order ($Y-X$ positive semidefinite) and PSD for symmetric positive semidefinite. Let $q\in\mathbb{N}$, let $D$ be positive definite, let $Q_y$ be PSD for every bit string $y\in\{0,1\}^q$, and let $T_{i,b}$ be PSD for $i\in\{0,\dots,q-1\}$ and $b\in\{0,1\}$. Assume:
--
--   1. $T_{i,0}+T_{i,1}\preceq D$ for every $i$;
--   2. $\varepsilon\ge0$, and $2\le\operatorname{tr}(Q_yD)\le2+\varepsilon$ for every $y$;
--   3. $\operatorname{tr}(Q_yT_{i,y_i})=2$ for every $y$ and every $i$.
--
--   **Theorem.** There exist real matrices $\rho_y$ ($y\in\{0,1\}^q$) and $F_{i,b}$ such that
--   $$\rho_y\succeq0,\quad\operatorname{tr}\rho_y=1,\quad F_{i,b}\succeq0,\quad F_{i,0}+F_{i,1}\preceq I,\quad\operatorname{tr}(\rho_yF_{i,y_i})\ge1-\varepsilon$$
--   for all $y$, $i$ and $b$.
--
--   The data $(Q_y,T_{i,b},D)$ might come from a PSD factorization, with $D$ a common upper bound for the pairs of tests. The theorem rescales such data into density matrices $\rho_y$ and two-outcome measurements $(F_{i,0},F_{i,1})$ in which bit $i$ of $y$ is decoded with success probability at least $1-\varepsilon$. Combined with the dimension bound for nearly perfect bit tests, it yields $|R|\ge2^{q-1}$ whenever $q\sqrt\varepsilon\le1/4$.
--
--   **Formalization Note** Bit strings are functions `Fin q → Bool`, with `false` and `true` playing the roles of $0$ and $1$. Positive definiteness is `Matrix.PosDef`, and `0 ≤ F i b` is taken in the `MatrixOrder` Loewner order, so it means that $F_{i,b}$ is PSD.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/BitTests.lean#L39-L80

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
universe u_1
open Matrix
open scoped MatrixOrder
variable {R : Type u_1} [Fintype R] [DecidableEq R]

theorem OAI.PerfectMatchingPSD.states_of_domination {q : ℕ}
    (Q : (Fin q → Bool) → Matrix R R ℝ) (T : Fin q → Bool → Matrix R R ℝ)
    (D : Matrix R R ℝ) (hD : D.PosDef)
    (hQ : ∀ y, (Q y).PosSemidef) (hT : ∀ i b, (T i b).PosSemidef)
    (hdom : ∀ i, T i false + T i true ≤ D)
    (ε : ℝ) (hε : 0 ≤ ε)
    (htr : ∀ y, 2 ≤ (Q y*D).trace ∧ (Q y*D).trace ≤ 2+ε)
    (hbit : ∀ y i, (Q y * T i (y i)).trace = 2) :
    ∃ (ρ : (Fin q → Bool) → Matrix R R ℝ) (F : Fin q → Bool → Matrix R R ℝ),
      (∀ y, (ρ y).PosSemidef) ∧ (∀ y, (ρ y).trace = 1) ∧
      (∀ i b, 0 ≤ F i b) ∧ (∀ i, F i false + F i true ≤ 1) ∧
      ∀ y i, 1-ε ≤ (ρ y*F i (y i)).trace := by sorry
