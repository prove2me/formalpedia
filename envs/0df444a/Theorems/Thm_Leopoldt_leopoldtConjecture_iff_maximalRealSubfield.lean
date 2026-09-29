-- Prove2me | Theorems.Thm_Leopoldt_leopoldtConjecture_iff_maximalRealSubfield
-- name    : Leopoldt.leopoldtConjecture_iff_maximalRealSubfield
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:39:20.029987+00:00
-- url     : https://prove2.me/theorems/47bf9dce-4781-40c5-881b-b4c6d5cb4cbc
-- title:
--   Leopoldt's conjecture holds for a CM field iff it holds for its maximal real subfield
-- statement:
--   Let $p$ be a prime and let $\mathbb{K}$ be a CM field with maximal totally real subfield $\mathbb{K}^+$. Then Leopoldt's conjecture holds for $\mathbb{K}$ at $p$ (i.e. $\mathcal{D}_L(\mathbb{K}) = 0$) if and only if it holds for $\mathbb{K}^+$ at $p$. This follows immediately from the equality of defects $\mathcal{D}_L(\mathbb{K}) = \mathcal{D}_L(\mathbb{K}^+)$.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1, p.4 ("For CM extensions K, the contraposition of the conjecture herewith reduces to ... K⁺"); uses IsCMField.units_rank_eq_units_rank (rk E(K) = rk E(K⁺)).

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldtConjecture_iff_maximalRealSubfield (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    LeopoldtConjecture p K ↔ LeopoldtConjecture p (maximalRealSubfield K) := by sorry
end Leopoldt
