-- Prove2me | Theorems.Thm_KaehlerDifferential_D_ne_zero_of_forall_pow_ne
-- name    : KaehlerDifferential.D_ne_zero_of_forall_pow_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/15492b05-7716-5b8e-a168-053530bdc446
-- title:
--   Non-p-th powers have non-zero absolute differential
-- statement:
--   Let $k$ be a field in a universe $u$, let $p$ be a natural number, assume $p$ is prime and that $k$ has exponential characteristic $p$ (so, $p$ being prime, $k$ has characteristic $p$), and let $c \in k$ be an element such that $b^p \neq c$ for every $b \in k$, i.e. $c$ is not a $p$-th power in $k$. The conclusion is that the universal derivation applied to $c$ is non-zero, namely $\mathrm{D}\,c \neq 0$ in the module of Kähler differentials $\Omega_{k/\bot}$ of $k$ over the bottom subfield $\bot \subseteq k$, that is over the prime subfield of $k$ (here the bottom element of the lattice of subfields of $k$, which in characteristic $p$ is the copy of $\mathbb{F}_p$ inside $k$). Equivalently, together with the vanishing $\mathrm{d}(b^p) = p\,b^{p-1}\,\mathrm{d}b = 0$, this identifies the kernel of $\mathrm{d} \colon k \to \Omega_{k/\mathbb{F}_p}$ with $k^p$, but only the stated implication is asserted.
--
--   This is the standard fact that, over the prime field in characteristic $p$, the kernel of the universal derivation of a field is exactly the subfield of $p$-th powers; classically it is read off from the theory of $p$-bases. It is used here in the proof of [`Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id`](thm.html#Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id), within the formal smoothness machinery for field and ring extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KaehlerDifferential_D_ne_zero_of_forall_pow_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem KaehlerDifferential.D_ne_zero_of_forall_pow_ne
    {k : Type u} [Field k] (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (c : k) (hc : ∀ b : k, b ^ p ≠ c) :
    KaehlerDifferential.D (⊥ : Subfield k) k c ≠ 0 := by sorry
