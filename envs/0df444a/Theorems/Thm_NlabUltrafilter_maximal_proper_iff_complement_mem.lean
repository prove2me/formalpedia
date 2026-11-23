-- Prove2me | Theorems.Thm_NlabUltrafilter_maximal_proper_iff_complement_mem
-- name    : NlabUltrafilter.maximal_proper_iff_complement_mem
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T20:27:45.333433+00:00
-- url     : https://prove2.me/theorems/7c1a6710-a22b-4939-8943-158ce58e8b77
-- title:
--   Maximal proper filters decide every subset
-- statement:
--   In classical logic, for any type $\alpha$ and filter $F$ on it, the following conditions are equivalent: (1) $F$ is nontrivial, and every nontrivial filter $G$ below $F$ in Mathlib’s filter order also satisfies $F \leq G$; (2) $F$ is nontrivial, and for every subset $s\subseteq\alpha$, either $s$ belongs to $F$ or its complement $\alpha\setminus s$ belongs to $F$. This is the proper-filter characterization of ultrafilters by deciding every subset or its complement.
-- source:
--   nLab, “Ultrafilters,” Definitions, https://ncatlab.org/nlab/show/ultrafilter#definitions; Mathlib, Mathlib.Order.Filter.Ultrafilter.Defs, https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Ultrafilter/Defs.html

import Mathlib

namespace NlabUltrafilter

theorem maximal_proper_iff_complement_mem {α : Type*} (F : Filter α) :
    (F.NeBot ∧ ∀ G : Filter α, G.NeBot → G ≤ F → F ≤ G) ↔
      (F.NeBot ∧ ∀ s : Set α, s ∈ F ∨ sᶜ ∈ F) := by sorry

end NlabUltrafilter
