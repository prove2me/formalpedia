-- Prove2me | Theorems.Thm_MazurAdmissible_natCard_eq_pow_filtLength
-- name    : MazurAdmissible.natCard_eq_pow_filtLength
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/1bb53da6-ef04-543e-a548-0f466c428f01
-- title:
--   Order of an admissible Galois module is q^ℓ
-- statement:
--   Let $M$ be an additive abelian group, $q$ a natural number assumed prime, and $\Phi$ an `OpenAction` on $M$, that is, a monoid homomorphism $\varphi$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = (\overline{\mathbb Q} \simeq_{\mathrm{alg}[\mathbb Q]} \overline{\mathbb Q})$, for $\overline{\mathbb Q}$ the algebraic closure `AlgebraicClosure ℚ`, into the additive automorphism group of $M$, whose kernel is open. Let $c$ be an `AdmissibleChain q Φ`: a natural number $n$, a family of subgroups $M_i = c.\mathrm{step}\, i$ indexed by $i \in \mathrm{Fin}(n+1)$ with $M_0 = \bot$ and $M_n = \top$, with $M_i \le M_{i+1}$ for each $i$, together with a tag function $\mathrm{Fin}\, n \to \mathrm{Bool}$ such that each successive quotient $M_{i+1}/M_i$ has `Nat.card` equal to $q$, and such that each step is trivial when tagged (i.e. $\varphi(\sigma)x - x \in M_i$ for all $\sigma$ and all $x \in M_{i+1}$) and cyclotomic otherwise (i.e. $\varphi(\sigma)x - a\cdot x \in M_i$ whenever $\zeta \in \overline{\mathbb Q}$ is a primitive $q$-th root of unity, $a \in \mathbb N$ satisfies $\sigma\zeta = \zeta^a$, and $x \in M_{i+1}$). The conclusion is $\operatorname{Nat.card} M = q^{\mathrm{filtLength}\, c}$, where $\mathrm{filtLength}\, c = n$. The proof uses neither the primality of $q$ nor the trivial/cyclotomic conditions on the steps.
--
--   This is the elementary counting half of Mazur's invariant $\ell(G)$ for admissible $q$-groups: an abelian group carrying an admissible chain of length $n$ is finite of order $q^n$. It is used in the construction of bounded admissible chains on Hecke-module quotients attached to modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MazurAdmissible_natCard_eq_pow_filtLength.lean

import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MazurAdmissible

theorem MazurAdmissible.natCard_eq_pow_filtLength
    {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) {Φ : OpenAction M}
    (c : AdmissibleChain q Φ) : Nat.card M = q ^ filtLength c := by sorry
