-- Prove2me | Theorems.Thm_Leopoldt_closure_range_diagonalUnits_subset_unitClosure
-- name    : Leopoldt.closure_range_diagonalUnits_subset_unitClosure
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:21:16.743801+00:00
-- url     : https://prove2.me/theorems/187389de-0cff-4804-84ce-14d22c824fe7
-- title:
--   The $p$-adic closure of the global units lies in $\bigcap_n \iota(E)U^{p^n}$
-- statement:
--   Let $K$ be a number field, $p$ a prime, $U=\prod_{\mathfrak p\mid p}\mathcal O_{\mathfrak p}^\times$ the semilocal units at $p$ and $\iota:E=\mathcal O_K^\times\to U$ the diagonal embedding. Then the topological closure of $\iota(E)$ in $U$ is contained in
--   $$\bar E=\bigcap_{n\ge 0}\iota(E)\cdot U^{p^{n+1}}.$$
--
--   This is the inclusion $\overline{\iota(E)}\subseteq\bigcap_n\iota(E)U^{p^n}$ of the identity $\bar E=\overline{\iota(E)}=\bigcap_n\iota(E)U^{p^n}$ in §1.1 of the source; it follows because the right-hand side is a closed subgroup containing $\iota(E)$. (The reverse inclusion can fail by a finite group of roots of unity of order prime to $p$ — e.g. for $K=\mathbb Q$, $p=7$ the intersection is $\mu_6$ while $\overline{\iota(E)}=\{\pm1\}$ — which does not affect $\mathbb Z_p$-ranks.)
-- source:
--   P. Mihăilescu, On CM ℤ_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (definition Ē = closure(ι(E)) = ⋂_{n>0} ι(E)·U^{p^n})

import Definitions.Def_LeopoldtDefect

namespace Leopoldt

theorem closure_range_diagonalUnits_subset_unitClosure (p : ℕ) [Fact p.Prime] (K : Type*)
    [Field K] [NumberField K] :
    closure (Set.range (diagonalUnits p K)) ⊆ (unitClosure p K : Set (SemilocalUnits p K)) := by sorry

end Leopoldt
