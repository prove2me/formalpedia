-- Prove2me | Theorems.Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm
-- name    : ModularForm.coeffHeckeT_coeffHeckeU_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d67181b2-d9a8-52ab-ab08-d4ed37010b41
-- title:
--   Coefficient operators Tₚ and U_q commute for coprime p,q
-- statement:
--   Let $k$ be an integer, let $p,q$ be natural numbers with $\gcd(p,q)=1$, and let $a:\mathbb{N}\to\mathbb{C}$ be an arbitrary sequence of complex numbers. The two coefficient-level operators involved are defined purely combinatorially: [`ModularForm.coeffHeckeU q`](def/ModularForm_HeckeOperator.html#L165) sends $a$ to the sequence $n\mapsto a(nq)$, and [`ModularForm.coeffHeckeT k p`](def/ModularForm_HeckeOperator.html#L162) sends $a$ to the sequence $n\mapsto a(np) + p^{k-1}a(n/p)$ when $p\mid n$, and $n\mapsto a(np)$ otherwise (the correction term being literally $\mathbf{1}_{p\mid n}\,(p:\mathbb{C})^{k-1}a(n/p)$, with $n/p$ natural division and the power taken in $\mathbb{C}$ with integer exponent). The assertion is the equality of functions $\mathbb{N}\to\mathbb{C}$
--   $$\mathrm{coeffHeckeT}_k^p\bigl(\mathrm{coeffHeckeU}^q a\bigr) = \mathrm{coeffHeckeU}^q\bigl(\mathrm{coeffHeckeT}_k^p a\bigr),$$
--   both sides sending $n$ to $a(npq) + \mathbf{1}_{p\mid n}\,p^{k-1}a((n/p)q)$. No modularity, growth or holomorphy hypothesis on $a$ is imposed: this is an identity about arbitrary complex sequences.
--
--   This is the commutation relation $T_pU_q = U_qT_p$ for coprime indices, read on $q$-expansion coefficients, as it holds classically for $T_p$ with $p\nmid N$ and $U_q$ with $q\mid N$ acting on $M_k(\Gamma_0(N))$. It is used by [`ModularFormClass.heckeT_heckeU_comm`](thm.html#ModularFormClass.heckeT_heckeU_comm) to transport the relation to the operators on modular forms themselves, and thence in [`CuspForm.exists_isNormalizedEigenform`](thm.html#CuspForm.exists_isNormalizedEigenform), the existence of a normalised eigenform in the relevant eigenspace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.coeffHeckeT_coeffHeckeU_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) : ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeU q a) = ModularForm.coeffHeckeU q (ModularForm.coeffHeckeT k p a) := by sorry
