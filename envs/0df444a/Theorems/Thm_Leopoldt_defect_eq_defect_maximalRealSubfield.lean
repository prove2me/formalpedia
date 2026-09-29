-- Prove2me | Theorems.Thm_Leopoldt_defect_eq_defect_maximalRealSubfield
-- name    : Leopoldt.defect_eq_defect_maximalRealSubfield
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:39:17.925986+00:00
-- url     : https://prove2.me/theorems/1c680494-9b66-4125-8824-9106af821bae
-- title:
--   The Leopoldt defect of a CM field equals that of its maximal real subfield
-- statement:
--   Let $p$ be a prime and let $\mathbb{K}$ be a CM field with maximal totally real subfield $\mathbb{K}^+$. Then the Leopoldt defects agree:
--   $$\mathcal{D}_L(\mathbb{K}) = \mathcal{D}_L(\mathbb{K}^+),$$
--   where $\mathcal{D}_L(\mathbb{L}) = \mathbb{Z}\text{-rk}\,E(\mathbb{L}) - \mathbb{Z}_p\text{-rk}\,\overline{E}(\mathbb{L})$ is the difference between the Dirichlet unit rank and the $\mathbb{Z}_p$-rank of the $p$-adic closure of the global units in the semilocal units at $p$. The reason is that $E(\mathbb{K}^+)$ has finite index in $E(\mathbb{K})$ (the unit ranks agree), so the $\mathbb{Z}_p$-ranks of the closures agree as well. No parity assumption on $p$ is needed.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1, p.4 ("For CM extensions K, the contraposition of the conjecture herewith reduces to ... K⁺"); uses IsCMField.units_rank_eq_units_rank (rk E(K) = rk E(K⁺)).

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_eq_defect_maximalRealSubfield (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    defect p K = defect p (maximalRealSubfield K) := by sorry
end Leopoldt
