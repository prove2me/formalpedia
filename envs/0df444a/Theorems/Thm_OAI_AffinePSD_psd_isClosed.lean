-- Prove2me | Theorems.Thm_OAI_AffinePSD_psd_isClosed
-- name    : OAI.AffinePSD.psd_isClosed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:14:11.548983+00:00
-- url     : https://prove2.me/theorems/96000d0f-ad95-47ae-b211-e531be606f35
-- title:
--   The real positive semidefinite matrices form a closed set
-- statement:
--   Let $R$ be a finite index set. The set of positive semidefinite real $R\times R$ matrices is closed:
--   $$
--   \{A\in\mathbb{R}^{R\times R}:A\succeq0\}\ \text{is closed.}
--   $$
--
--   Here positive semidefinite means symmetric with $x^{\mathsf T}Ax\ge0$ for all $x\in\mathbb{R}^R$. Closedness is what lets limits of positive semidefinite certificates remain certificates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PSDTopology.lean#L11-L27

import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation

open OAI OAI.AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

omit [Fintype I] [DecidableEq R] in
theorem OAI.AffinePSD.psd_isClosed : IsClosed {A : Matrix R R ℝ | A.PosSemidef} := by sorry
