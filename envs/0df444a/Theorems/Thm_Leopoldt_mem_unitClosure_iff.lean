-- Prove2me | Theorems.Thm_Leopoldt_mem_unitClosure_iff
-- name    : Leopoldt.mem_unitClosure_iff
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:13:59.819878+00:00
-- url     : https://prove2.me/theorems/3db93b95-2695-4590-b1f9-be9b7ce3a7c8
-- title:
--   Elements of $\bigcap_n \iota(E)U^{p^n}$: closure of $\iota(E)$ times prime-to-$p$ torsion
-- statement:
--   Let $p$ be a prime, $K$ a number field, $U$ the semilocal units at $p$, $\iota:E\to U$ the diagonal embedding of the global units, and $\bar E=\bigcap_{n}\iota(E)\,U^{p^n}$ (the platform's `unitClosure`). Then $u\in \bar E$ if and only if $u=c\,t$ where $c$ lies in the topological closure $\overline{\iota(E)}$ of $\iota(E)$ in $U$ and $t\in U$ is a torsion element of order prime to $p$. In other words
--   $$\bigcap_{n\ge1}\iota(E)\,U^{p^n}\;=\;\overline{\iota(E)}\cdot\mu'(U),$$
--   where $\mu'(U)$ denotes the prime-to-$p$ torsion of $U$. This corrects the identification $\bar E=\overline{\iota(E)}$ in the source: the intersection may be strictly larger (e.g. $K=\mathbb Q$, $p=7$ gives $\mu_6$ versus $\{\pm1\}$), though only by a finite group, so the $\mathbb Z_p$-ranks agree.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1, p.3 (definition of Ē = ⋂_n ι(E)·U^{p^n}); J. Neukirch, Algebraic Number Theory, Ch. II, Prop. 5.7 (structure U ≅ μ_{q-1} × U^{(1)} of local units, U^{(1)} a finitely generated ℤ_p-module).

import Definitions.Def_LeopoldtDefect

namespace Leopoldt
theorem mem_unitClosure_iff (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    (u : SemilocalUnits p K) :
    u ∈ unitClosure p K ↔ ∃ c ∈ closure (Set.range (diagonalUnits p K)),
      ∃ t : SemilocalUnits p K, (∃ m : ℕ, m.Coprime p ∧ t ^ m = 1) ∧ c * t = u := by sorry
end Leopoldt
