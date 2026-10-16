-- Prove2me | Theorems.Thm_OAI_Paper256_isOpen_posDef
-- name    : OAI.Paper256.isOpen_posDef
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:08:49.791714+00:00
-- url     : https://prove2.me/theorems/dca09368-2af0-4c21-bfdf-489d1414d135
-- title:
--   Positive definite matrices form an open subset of the symmetric matrices
-- statement:
--   For $n\in\mathbb{N}$ let $\mathrm{Sym}_n$ be the real vector space of symmetric $n\times n$ real matrices, with its standard topology (for instance the one induced by the operator norm; all norms on this finite-dimensional space are equivalent). Then the set of positive definite matrices
--   $$\mathcal P_n=\{X\in\mathrm{Sym}_n:\ v^\top Xv>0\ \text{ for all }v\in\mathbb{R}^n\setminus\{0\}\}$$
--   is open in $\mathrm{Sym}_n$.
--
--   Openness is what allows small perturbations: if $X\succ0$ and $H$ is any symmetric direction, then $X\pm\varepsilon H\succ0$ for small $\varepsilon>0$. This is used to show $\ker D(I)\subseteq\ker D(X)$ for positive linear maps $D$, and in the analysis of spectrahedral representations of cones.
--
--   **Formalization Note** The space is `Sym n`, the self-adjoint part of the real $n\times n$ matrices, with the subspace topology; the metric used in the proof comes from the scoped operator norm `Matrix.Norms.L2Operator`. A companion statement for matrices indexed by an arbitrary finite type is proved separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilOrder.lean#L54-L68

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum

open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

theorem OAI.Paper256.isOpen_posDef (n : ℕ) : IsOpen {X : Sym n | (X : Mat n ℝ).PosDef} := by sorry
