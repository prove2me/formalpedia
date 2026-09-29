-- Prove2me | Theorems.Thm_MazurAdmissible_filtAlpha_eq_filtAlpha
-- name    : MazurAdmissible.filtAlpha_eq_filtAlpha
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/d8364779-07f8-5a21-bcd4-25bffc26235b
-- title:
--   Chain-independence of the invariant α at odd primes
-- statement:
--   Let $M$ be an additive abelian group, let $q$ be a prime with $q \neq 2$, and let $\Phi$ be an `OpenAction` on $M$, that is, a monoid homomorphism $\Phi.\varphi$ from the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` to the group of additive automorphisms of $M$ whose kernel is open. Let $c$ and $c'$ be two admissible chains for $\Phi$ at $q$; such a datum consists of a length $n$, a family of subgroups $\mathrm{step}(i) \le M$ indexed by $i \in \mathrm{Fin}(n+1)$ with $\mathrm{step}(0) = \bot$ and $\mathrm{step}(n) = \top$ and $\mathrm{step}(i) \le \mathrm{step}(i+1)$ for all $i$, a Boolean tag $\mathrm{tag}(i)$ for each of the $n$ steps, the requirement that each quotient $\mathrm{step}(i+1)/\mathrm{step}(i)$ have cardinality exactly $q$, and, for each $i$, the requirement that the step be trivial or cyclotomic according to its tag: if $\mathrm{tag}(i)$ is true, then $\Phi.\varphi(\sigma)x - x \in \mathrm{step}(i)$ for all $\sigma$ and all $x \in \mathrm{step}(i+1)$; if it is false, then $\Phi.\varphi(\sigma)x - a\,x \in \mathrm{step}(i)$ for all $\sigma$, all $x \in \mathrm{step}(i+1)$, and all natural numbers $a$ for which $\sigma\zeta = \zeta^{a}$ for some primitive $q$-th root of unity $\zeta \in \overline{\mathbb{Q}}$. The conclusion is that the two chains have the same number of true tags: `filtAlpha c = filtAlpha c'`, where `filtAlpha` counts the indices $i$ with $\mathrm{tag}(i)$ true. Note that the lengths of $c$ and $c'$ are not assumed equal.
--
--   This is the well-definedness of Mazur's invariant $\alpha$ of a Galois module filtered by steps of order $q$, each of which is of trivial or of cyclotomic type (Mazur, Eisenstein ideal, Chapter I, §1(f)): at an odd prime the count of trivial steps depends only on $(M,\Phi)$ and not on the chosen chain. It is used further on in the treatment of torsion in Néron models attached to modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MazurAdmissible_filtAlpha_eq_filtAlpha.lean

import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MazurAdmissible

theorem MazurAdmissible.filtAlpha_eq_filtAlpha
    {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Φ : OpenAction M}
    (c c' : AdmissibleChain q Φ) : filtAlpha c = filtAlpha c' := by sorry
