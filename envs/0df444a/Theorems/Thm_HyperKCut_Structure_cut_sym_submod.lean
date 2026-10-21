-- Prove2me | Theorems.Thm_HyperKCut_Structure_cut_sym_submod
-- name    : HyperKCut.Structure.cut_sym_submod
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:05.856971+00:00
-- url     : https://prove2.me/theorems/72a9120a-22f6-419a-9b29-0927cfc7999e
-- title:
--   §3, p. 7 — symmetry and submodularity of the cut value
-- statement:
--   For every finite unit-cost hypergraph $G=(V,E)$, its cut value $d$ satisfies
--
--   $$d(V\setminus A)=d(A),\qquad d(A\cap B)+d(A\cup B)\le d(A)+d(B)$$
--
--   for all vertex sets $A,B\subseteq V$. This is the symmetry and submodularity used in the paper's uncrossing arguments.
--
--   **Formalization Note** The natural-number cut counts are cast to real numbers to use the published predicates `SymmetricSetFun` and `Submodular`.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 7 (PDF 8), §3, displayed symmetry and submodularity facts

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- §3, p. 7: the hypergraph cut function is symmetric and submodular. -/
theorem cut_sym_submod (H : Hypergraph V) :
    NonmonotoneSubmod.Shared.SymmetricSetFun (fun A => (d H A : ℝ)) ∧
    NonmonotoneSubmod.Shared.Submodular (fun A => (d H A : ℝ)) := by sorry

end HyperKCut.Structure
