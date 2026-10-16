-- Prove2me | Theorems.Thm_OAI_Paper256_FiniteMatrix_isOpen_posDef
-- name    : OAI.Paper256.FiniteMatrix.isOpen_posDef
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:19:04.332982+00:00
-- url     : https://prove2.me/theorems/cafe0368-2753-4af2-ac4b-4cecc5d14342
-- title:
--   Positive definite matrices are open among symmetric matrices indexed by any finite set
-- statement:
--   Let $\iota$ be a finite index set and let $\mathrm{Sym}_\iota$ be the real vector space of symmetric matrices $X=(X_{ij})_{i,j\in\iota}$ with real entries, with its standard finite-dimensional topology. Then the set of positive definite matrices
--   $$\{X\in\mathrm{Sym}_\iota:\ v^\top Xv>0\ \text{ for all }v\in\mathbb{R}^\iota\setminus\{0\}\}$$
--   is open in $\mathrm{Sym}_\iota$.
--
--   This is the openness of the positive definite cone for matrices indexed by an arbitrary finite type, for instance block matrices indexed by a disjoint union $\{1,\dots,a\}\sqcup\{1,\dots,c\}$. It is used to show that small perturbations of a positive definite block matrix remain positive definite.
--
--   **Formalization Note** The space is `selfAdjoint (Matrix ι ι ℝ)` with the subspace topology, for a `Fintype` index type with decidable equality; the proof uses the operator norm from the scoped instance `Matrix.Norms.L2Operator`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/FiniteTopology.lean#L59-L73

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology

open OAI OAI.Paper256 OAI.Paper256.FiniteMatrix
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder
universe u v

theorem OAI.Paper256.FiniteMatrix.isOpen_posDef (ι : Type u) [Fintype ι] [DecidableEq ι] : IsOpen {X : selfAdjoint (Matrix ι ι ℝ) | (X : Matrix ι ι ℝ).PosDef} := by sorry
