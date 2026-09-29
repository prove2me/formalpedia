-- Prove2me | Theorems.Thm_Leopoldt_mem_iInf_powMonoidHom_range_iff
-- name    : Leopoldt.mem_iInf_powMonoidHom_range_iff
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:14:08.01004+00:00
-- url     : https://prove2.me/theorems/2be0df7c-adf4-4105-add4-e0c2b19f04d9
-- title:
--   $\bigcap_n U^{p^n}$ is the prime-to-$p$ torsion of the semilocal units
-- statement:
--   Let $p$ be a prime, $K$ a number field and $U=\prod_{\mathfrak p\mid p}\mathcal O_{\mathfrak p}^\times$ the group of semilocal units at $p$. Then the infinitely $p$-divisible elements of $U$ are exactly its torsion elements of order prime to $p$:
--   $$\bigcap_{n\ge 1} U^{p^n} \;=\; \{\,u\in U \;:\; u^m=1 \text{ for some } m\in\mathbb N \text{ with } \gcd(m,p)=1\,\}.$$
--   In terms of the decomposition $U\cong \mu'\times U_p$ with $\mu'$ the finite group of roots of unity of order prime to $p$ and $U_p$ pro-$p$, this says $\bigcap_n U^{p^n}=\mu'$.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1, p.3 (definition of Ē = ⋂_n ι(E)·U^{p^n}); J. Neukirch, Algebraic Number Theory, Ch. II, Prop. 5.7 (structure U ≅ μ_{q-1} × U^{(1)} of local units, U^{(1)} a finitely generated ℤ_p-module).

import Definitions.Def_LeopoldtDefect

namespace Leopoldt
theorem mem_iInf_powMonoidHom_range_iff (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [NumberField K] (u : SemilocalUnits p K) :
    u ∈ (⨅ n : ℕ, (powMonoidHom (p ^ (n + 1)) : SemilocalUnits p K →* SemilocalUnits p K).range) ↔
      ∃ m : ℕ, m.Coprime p ∧ u ^ m = 1 := by sorry
end Leopoldt
