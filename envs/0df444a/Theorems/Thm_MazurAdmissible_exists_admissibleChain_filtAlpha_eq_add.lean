-- Prove2me | Theorems.Thm_MazurAdmissible_exists_admissibleChain_filtAlpha_eq_add
-- name    : MazurAdmissible.exists_admissibleChain_filtAlpha_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/0c713976-3b4c-52d9-b626-0ecdb67cfd13
-- title:
--   Splicing admissible chains: α and length are additive
-- statement:
--   Let $M$ be an additive commutative group, $q$ a prime natural number, and $\Phi$ an `OpenAction` on $M$, that is a monoid homomorphism $\Phi.\varphi$ from the group of field automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` over $\mathbb{Q}$ to the additive automorphisms of $M$ whose kernel is open. Let $N$ be an additive subgroup of $M$ stable under the action, in the sense that $\Phi.\varphi\,\sigma\,x \in N$ for every $\sigma$ and every $x \in N$; let $\Phi_N$ be an open-kernel action on $N$ and $\Phi_Q$ one on $M/N$, compatible with $\Phi$ pointwise: $\Phi_N.\varphi\,\sigma\,x = \Phi.\varphi\,\sigma\,x$ inside $M$ for $x \in N$, and $\Phi_Q.\varphi\,\sigma$ applied to the class of $x$ is the class of $\Phi.\varphi\,\sigma\,x$. Given admissible chains $c_N$ for $q, \Phi_N$ and $c_Q$ for $q, \Phi_Q$ — each consisting of an increasing chain of subgroups from $\bot$ to $\top$ indexed by `Fin (n+1)`, with every successive quotient of cardinality exactly $q$, together with a Boolean tag on each of the $n$ steps marking it trivial (all $\sigma$ act on the upper group as the identity modulo the lower) or cyclotomic (for every primitive $q$-th root of unity $\zeta$ and every $a$ with $\sigma\zeta = \zeta^{a}$, $\sigma$ acts by $a$ modulo the lower group) — the conclusion is that there exists an admissible chain $c$ for $q, \Phi$ whose number of true tags is the sum of those of $c_N$ and $c_Q$ and whose length $c.n$ is the sum of the two lengths.
--
--   This is the closure of Mazur's admissible filtrations under extension along a short exact sequence $0 \to N \to M \to M/N \to 0$ of Galois modules, with the invariants $\alpha$ (number of trivial steps) and the length $\ell$ adding: the chain of $N$ is followed by the preimages of the chain of $M/N$. It supplies the existence of admissible chains in the extension, and is used by [`MazurAdmissible.AdmissibleChain.nonempty_of_addSubgroup`](thm.html#MazurAdmissible.AdmissibleChain.nonempty_of_addSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MazurAdmissible_exists_admissibleChain_filtAlpha_eq_add.lean

import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MazurAdmissible

theorem MazurAdmissible.exists_admissibleChain_filtAlpha_eq_add
    {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) (Φ : OpenAction M)
    (N : AddSubgroup M) (hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ N, Φ.φ σ x ∈ N)
    (ΦN : OpenAction ↥N) (hΦN : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥N), (ΦN.φ σ x : M) = Φ.φ σ x)
    (ΦQ : OpenAction (M ⧸ N))
    (hΦQ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M), ΦQ.φ σ (QuotientAddGroup.mk x) = QuotientAddGroup.mk (Φ.φ σ x))
    (cN : AdmissibleChain q ΦN) (cQ : AdmissibleChain q ΦQ) :
    ∃ c : AdmissibleChain q Φ,
      filtAlpha c = filtAlpha cN + filtAlpha cQ ∧ filtLength c = filtLength cN + filtLength cQ := by sorry
