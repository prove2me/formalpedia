-- Prove2me | Theorems.Thm_OAI_Paper256_isClosed_posSemidef
-- name    : OAI.Paper256.isClosed_posSemidef
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:09:12.480513+00:00
-- url     : https://prove2.me/theorems/b6cc4fc7-ef46-4bf0-870f-e321d680bc53
-- title:
--   Positive semidefinite matrices form a closed subset of the symmetric matrices
-- statement:
--   For $n\in\mathbb{N}$ let $\mathrm{Sym}_n$ be the real vector space of symmetric $n\times n$ real matrices with its standard finite-dimensional topology. Then the positive semidefinite cone
--   $$\mathcal S_n^{+}=\{X\in\mathrm{Sym}_n:\ v^\top Xv\ge0\ \text{ for all }v\in\mathbb{R}^n\}$$
--   is a closed subset of $\mathrm{Sym}_n$.
--
--   Closedness allows one to pass to limits in positivity statements: if $X_k\to X$ and every $X_k$ is positive semidefinite, then so is $X$. It is used to transfer positive semidefiniteness to limits of rescaled or regularized matrices when a spectrahedral representation is normalized.
--
--   **Formalization Note** The space is `Sym n` with the subspace topology coming from the scoped operator norm `Matrix.Norms.L2Operator`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilTopology.lean#L19-L35

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

open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder
universe u

theorem OAI.Paper256.isClosed_posSemidef (n : ℕ) : IsClosed {X : Sym n | (X : Mat n ℝ).PosSemidef} := by sorry
