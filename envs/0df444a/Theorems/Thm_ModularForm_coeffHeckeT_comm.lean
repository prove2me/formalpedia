-- Prove2me | Theorems.Thm_ModularForm_coeffHeckeT_comm
-- name    : ModularForm.coeffHeckeT_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/f18f7626-ec63-50ae-b63e-610da651f925
-- title:
--   Coefficient Hecke operators commute at coprime levels
-- statement:
--   Fix an integer weight $k$, natural numbers $p,q$ with $\mathrm{Nat.Coprime}\ p\ q$ (that is, $\gcd(p,q)=1$), and an arbitrary sequence $a\colon\mathbb N\to\mathbb C$. Here [`ModularForm.coeffHeckeT k p`](def/ModularForm_HeckeOperator.html#L162) is the operator on sequences defined coefficientwise by
--   $$(\mathrm{coeffHeckeT}\,k\,p\,a)(n)=a(np)+\begin{cases}(p:\mathbb C)^{k-1}\,a(n/p)&\text{if }p\mid n,\\0&\text{otherwise,}\end{cases}$$
--   where $n/p$ is natural-number division and $(p:\mathbb C)^{k-1}$ is the integer power of the complex number $p$ (so the exponent may be negative, and $0^{k-1}$ is interpreted by the usual conventions when $p=0$). The assertion is the equality of the two sequences $\mathbb N\to\mathbb C$ obtained by applying these operators in the two orders:
--   $$\mathrm{coeffHeckeT}\,k\,p\,(\mathrm{coeffHeckeT}\,k\,q\,a)=\mathrm{coeffHeckeT}\,k\,q\,(\mathrm{coeffHeckeT}\,k\,p\,a).$$
--   No primality of $p$ or $q$, and no positivity, is assumed beyond coprimality; the statement is purely one about sequences, with no modularity hypothesis on $a$.
--
--   This is the coefficient-side form of the commutation relation $T_pT_q=T_qT_p$ for Hecke operators at coprime indices, read on $q$-expansions. It is used to obtain commutativity of the Hecke operators acting on modular forms, [`ModularFormClass.heckeT_heckeT_comm`](thm.html#ModularFormClass.heckeT_heckeT_comm), and thence in the construction of normalised eigenforms, [`CuspForm.exists_isNormalizedEigenform`](thm.html#CuspForm.exists_isNormalizedEigenform).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_coeffHeckeT_comm.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.coeffHeckeT_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) : ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeT k q a) = ModularForm.coeffHeckeT k q (ModularForm.coeffHeckeT k p a) := by sorry
