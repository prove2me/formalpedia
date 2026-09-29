-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_modulus_complex_eq_nnnorm_sq
-- name    : LanglandsTunnell.TateLocal.modulus_complex_eq_nnnorm_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/b7d42dc5-766a-5b74-967d-6dc8b7875fab
-- title:
--   The Tate-local modulus on ℂ is |z|²
-- statement:
--   For every complex number $z$, the quantity `modulus z` equals $\|z\|_{\geq 0}^2$, the square of the complex absolute value taken as a non-negative real. Here `modulus` is the project's local modulus function on a field: for $a$ in a field $K$ it is defined to be $0$ when $a = 0$, and otherwise the value at the unit determined by $a$ of Mathlib's `distribHaarChar K`, i.e. the non-negative real scalar by which multiplication by $a$ scales any additive Haar measure on $K$. Thus the assertion is that on $\mathbb{C}$, viewed as a locally compact topological field with its additive Haar (Lebesgue) measure, multiplication by a non-zero $z$ multiplies Haar measure by $|z|^2$, while the modulus of $0$ is $0$, consistent with $\|0\|^2 = 0$. There are no further hypotheses: the statement is a closed universally quantified identity in $\mathbb{N}\mathbb{N}$-valued non-negative reals over all $z \in \mathbb{C}$.
--
--   This is the complex archimedean case of the computation of the normalised absolute value (module) of a local field in Tate's local theory, the companion of the real case $|x|$ and of the non-archimedean case. It is used in the construction of archimedean data for the converse-theorem input in the Langlands–Tunnell argument, via [`LanglandsTunnell.Converse.exists_archDatumC_W_ne_zero`](thm.html#LanglandsTunnell.Converse.exists_archDatumC_W_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_modulus_complex_eq_nnnorm_sq.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.modulus_complex_eq_nnnorm_sq :
    ∀ (z : ℂ), modulus z = ‖z‖₊ ^ 2 := by sorry
