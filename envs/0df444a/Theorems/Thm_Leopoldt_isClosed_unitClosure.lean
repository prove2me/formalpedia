-- Prove2me | Theorems.Thm_Leopoldt_isClosed_unitClosure
-- name    : Leopoldt.isClosed_unitClosure
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:21:25.758155+00:00
-- url     : https://prove2.me/theorems/16b54d26-b6e8-464e-9790-acad723ba470
-- title:
--   $\bar E=\bigcap_n \iota(E)U^{p^n}$ is closed in the semilocal units
-- statement:
--   Let $K$ be a number field, $p$ a prime, $U=\prod_{\mathfrak p\mid p}\mathcal O_{\mathfrak p}^\times$ the semilocal units at $p$, and $\iota:E=\mathcal O_K^\times\to U$ the diagonal embedding of the global units. Then the subgroup
--   $$\bar E=\bigcap_{n\ge 0}\iota(E)\cdot U^{p^{n+1}}$$
--   (the platform's `unitClosure p K`) is a **closed** subgroup of $U$.
--
--   Indeed each $\iota(E)\cdot U^{p^{n+1}}$ contains the open subgroup $U^{p^{n+1}}$, so it is open, and an open subgroup of a topological group is closed; an intersection of closed sets is closed.
-- source:
--   P. Mihăilescu, On CM ℤ_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (definition Ē = closure(ι(E)) = ⋂_{n>0} ι(E)·U^{p^n}); J. Neukirch, Algebraic Number Theory, Ch. II §5 (the p-adic logarithm/exponential and the multiplicative group of a p-adic field: for a p-adic field the subgroup of n-th powers of units is open)

import Definitions.Def_LeopoldtDefect

namespace Leopoldt

theorem isClosed_unitClosure (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    IsClosed (unitClosure p K : Set (SemilocalUnits p K)) := by sorry

end Leopoldt
