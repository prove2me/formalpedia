-- Prove2me | Theorems.Thm_LanglandsTunnell_sum_mulChar_norm_mul_addChar_trace_eq_gaussSum_pow_three_of_finrank_eq_three
-- name    : LanglandsTunnell.sum_mulChar_norm_mul_addChar_trace_eq_gaussSum_pow_three_of_finrank_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/dbd67a48-bcd1-57f0-9442-1c0e83b4f240
-- title:
--   Hasse–Davenport lifting relation in degree three
-- statement:
--   Let $F$ be a finite field and let $F'$ be a finite field equipped with an $F$-algebra structure such that $F'$ has dimension $3$ as an $F$-vector space. Let $\chi \colon F^\times \to \mathbb{C}$ be a multiplicative character of $F$ with complex values (in the Mathlib sense of `MulChar F ℂ`, extended by $0$ outside the units), assumed not to be the trivial character $1$, and let $\psi$ be an additive character of $F$ with values in $\mathbb{C}$. Then
--   $$\sum_{y \in F'} \chi\bigl(N_{F'/F}(y)\bigr)\,\psi\bigl(\mathrm{Tr}_{F'/F}(y)\bigr) = \bigl(\textstyle\sum_{x \in F} \chi(x)\,\psi(x)\bigr)^{3},$$
--   where the norm and trace are the algebra norm and algebra trace of the extension $F'/F$ and the right-hand side is the cube of the Gauss sum $\mathrm{gaussSum}(\chi,\psi)$. Equivalently, the Gauss sum attached to the lifted pair $(\chi \circ N_{F'/F},\ \psi \circ \mathrm{Tr}_{F'/F})$ on $F'$ is the cube of the Gauss sum of $(\chi,\psi)$ on $F$. No primitivity or non-triviality is assumed of $\psi$, and $F'$ is not required to be presented as a specific cubic extension beyond the degree hypothesis.
--
--   This is the Hasse–Davenport lifting relation in the special case of a cubic extension of finite fields: lifting a multiplicative character through the norm and the additive character through the trace cubes the Gauss sum. It is used in the local computation of root numbers, namely in [`LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_three`](thm.html#LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_three), where a character obtained by composition with a norm has inertial degree three.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_sum_mulChar_norm_mul_addChar_trace_eq_gaussSum_pow_three_of_finrank_eq_three.lean

import Mathlib.NumberTheory.GaussSum
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.sum_mulChar_norm_mul_addChar_trace_eq_gaussSum_pow_three_of_finrank_eq_three
    (F : Type) [Field F] [Fintype F] (F' : Type) [Field F'] [Algebra F F'] [Fintype F']
    (h3 : Module.finrank F F' = 3) (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) :
    ∑ y : F', χ (Algebra.norm F y) * ψ (Algebra.trace F F' y) = (gaussSum χ ψ) ^ 3 := by sorry
