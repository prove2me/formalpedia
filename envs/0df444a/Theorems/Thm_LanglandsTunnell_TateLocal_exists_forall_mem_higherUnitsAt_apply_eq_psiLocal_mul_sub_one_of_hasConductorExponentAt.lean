-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt
-- name    : LanglandsTunnell.TateLocal.exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/9cbe291e-d9db-5fde-9f60-32020bd8af5f
-- title:
--   Additive duality on the upper conductor filtration
-- statement:
--   Let $K$ be a number field and $v$ a nonzero prime of its ring of integers, and write $K_v$ for the $v$-adic completion. Let $\chi \colon K_v^\times \to \mathbb{C}^\times$ be a homomorphism of multiplicative monoids (no continuity is assumed) and let $a$ be a natural number such that `HasConductorExponentAt K v χ a` holds, i.e. $\chi$ is trivial on the set `higherUnitsAt K v a` and for every $m < a$ there is an element of `higherUnitsAt K v m` on which $\chi$ is nontrivial; here `higherUnitsAt K v n` consists of those units $u$ of $K_v$ with $\mathrm{v}(u) = 1$ and, unless $n = 0$, with $\mathrm{v}(u - 1) \le \exp(-n)$ in the value group. The conclusion is that there exists $c \in K_v^\times$ such that for every $u \in$ `higherUnitsAt K v` $(\lfloor (a-1)/2\rfloor + 1)$ — truncated subtraction and division of natural numbers, so the index is $1$ when $a \le 2$ — one has $\chi(u) = \psi_{K,v}\bigl(c\,(u-1)\bigr)$, where $\psi_{K,v}$ is `psiLocal K v`, the composite of the standard additive character of the adele ring of $K$ with the additive embedding of $K_v$ into the adeles at the place $v$.
--
--   This is the additive duality statement for the conductor filtration: on the upper half of the filtration a multiplicative character becomes an additive character, hence is given by translation of the fixed local additive character $\psi_{K,v}$ by a single element $c$, the element customarily used to parametrise the local root number. It is the source of the explicit formulae for local epsilon factors and root numbers used in the local computations and in the converse-theorem arguments of the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain

theorem
LanglandsTunnell.TateLocal.exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (hχ : HasConductorExponentAt K v χ a) :
    ∃ c : (v.adicCompletion K)ˣ, ∀ u ∈ higherUnitsAt K v ((a - 1) / 2 + 1),
      (χ u : ℂ) = psiLocal K v ((c : v.adicCompletion K) * ((u : v.adicCompletion K) - 1)) := by sorry
