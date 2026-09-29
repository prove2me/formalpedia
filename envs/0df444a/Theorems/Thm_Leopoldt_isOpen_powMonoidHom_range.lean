-- Prove2me | Theorems.Thm_Leopoldt_isOpen_powMonoidHom_range
-- name    : Leopoldt.isOpen_powMonoidHom_range
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:21:12.808811+00:00
-- url     : https://prove2.me/theorems/368a636e-eff0-4cee-b767-71e34aee6265
-- title:
--   The $p^n$-th powers form an open subgroup of the semilocal units
-- statement:
--   Let $K$ be a number field, $p$ a prime, and let
--   $$U=\prod_{\mathfrak p\mid p}\mathcal O_{\mathfrak p}^\times$$
--   be the group of semilocal units at $p$ (the product of the unit groups of the completed rings of integers at the primes of $K$ above $p$), with the product topology. Then for every $n\ge 0$ the subgroup
--   $$U^{p^n}=\{u^{p^n} : u\in U\}$$
--   of $p^n$-th powers is **open** in $U$.
--
--   Equivalently, $U^{p^n}$ contains a neighbourhood of $1$. Concretely, if $\pi_{\mathfrak p}=\|p\|_{\mathfrak p}<1$ denotes the absolute value of $p$ in $K_{\mathfrak p}$, every $x\in\mathcal O_{\mathfrak p}^\times$ with $\|x-1\|\le \pi_{\mathfrak p}^{\,n+3}$ is a $p^n$-th power of a unit (Hensel/Newton approximation, or the $p$-adic logarithm and exponential). This is the basic fact making $\iota(E)\cdot U^{p^n}$ an open (hence closed) subgroup, so that the intersection $\bar E=\bigcap_n \iota(E)U^{p^n}$ of §1.1 of the source is closed.
-- source:
--   P. Mihăilescu, On CM ℤ_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (definition Ē = closure(ι(E)) = ⋂_{n>0} ι(E)·U^{p^n}); J. Neukirch, Algebraic Number Theory, Ch. II §5 (the p-adic logarithm/exponential and the multiplicative group of a p-adic field: for a p-adic field the subgroup of n-th powers of units is open)

import Definitions.Def_LeopoldtDefect

namespace Leopoldt

theorem isOpen_powMonoidHom_range (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    (n : ℕ) :
    IsOpen ((powMonoidHom (p ^ n) : SemilocalUnits p K →* SemilocalUnits p K).range :
      Set (SemilocalUnits p K)) := by sorry

end Leopoldt
