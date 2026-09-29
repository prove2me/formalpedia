-- Prove2me | Theorems.Thm_NumberField_InfinitePlace_isUnramifiedIn_of_pow_eq
-- name    : NumberField.InfinitePlace.isUnramifiedIn_of_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/4827c07a-e532-5f13-9316-de181a37f5d3
-- title:
--   Infinite places unramified in Kummer extensions E(u^{1/p})
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an $E$-algebra, let $p$ be a prime, and assume the set of primitive $p$-th roots of unity in $E$ is nonempty. Let $u \in E$ and $\alpha \in M$ satisfy $\alpha^{p} = u$ (the image of $u$ under the structure map $E \to M$), and assume $\alpha$ generates $M$ over $E$, in the sense that the intermediate field $E(\alpha)$ of $M$ is all of $M$. Let $w$ be an infinite place of $E$, and assume that if $w$ is real then $u$ becomes a $p$-th power in the completion $E_w$, i.e. there is $b \in E_w$ with $\iota(u) = b^{p}$ for the canonical map $\iota : E \to E_w$. The conclusion is that $w$ is unramified in $M$: every infinite place $w'$ of $M$ whose restriction to $E$ along $E \to M$ equals $w$ is unramified over $E$, that is, $w'$ is real or the place of $E$ below it is complex. The hypothesis on $u$ is imposed only at real $w$; at complex $w$ the assertion is unconditional.
--
--   This is the archimedean counterpart of the local splitting criterion for Kummer extensions $E(u^{1/p})/E$: the condition that $u$ be a local $p$-th power at $w$ forces the places above $w$ to be unramified. It is used to verify the infinite-place hypothesis in [`NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom`](thm.html#NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlace_isUnramifiedIn_of_pow_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.InfinitePlace.isUnramifiedIn_of_pow_eq
    (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p E).Nonempty) (u : E) (α : M) (hα : α ^ p = algebraMap E M u)
    (hgen : IntermediateField.adjoin E {α} = ⊤)
    (w : NumberField.InfinitePlace E)
    (hb : w.IsReal → ∃ b : w.Completion, algebraMap E w.Completion u = b ^ p) :
    w.IsUnramifiedIn M := by sorry
