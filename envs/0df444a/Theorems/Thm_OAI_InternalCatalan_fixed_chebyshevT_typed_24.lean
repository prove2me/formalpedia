-- Prove2me | Theorems.Thm_OAI_InternalCatalan_fixed_chebyshevT_typed_24
-- name    : OAI.InternalCatalan.fixed_chebyshevT_typed_24
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T22:00:46.694131+00:00
-- url     : https://prove2.me/theorems/a2d483d3-b99f-4201-ae47-2c96b773d38f
-- title:
--   OpenAI Catalan, §4.4 — the Chebyshev polynomial T₂₄ over ℤ, explicitly
-- statement:
--   Let $T_{24}\in\mathbb Z[x]$ be the Chebyshev polynomial of the first kind of degree $24$ (Mathlib's `Polynomial.Chebyshev.T ℤ 24`, defined by $T_0=1$, $T_1=x$, $T_{n+2}=2xT_{n+1}-T_n$), and let $P$ be the explicit integer polynomial of the definitions bundle `OAICatalanChebyshevData` (`fixedChebyshevTData_24`, a sum of monomials $c_jx^j$ with the integer coefficients written out). Then
--
--   $$T_{24}=P .$$
--
--   The row polynomials of the fixed matrix $\mathcal B$ (paper, §4.4) are built from $t^{62}T_u(1/t)$ and $t^{62}U_{u-1}(1/t)$ for $u\le44$; OpenAI's certificate computes the needed $T_u$ and $U_u$ with explicit integer coefficients through the three-term recurrence, and this is one anchor of that computation.
--
--   OpenAI, p. 23: “These are ordinary integer polynomials: they are $E_m=t^{62}T_m(1/t)$ and $I_m=t^{62}U_{m-1}(1/t)$.”
--
--   **Formalization note.** The statement is an equality in $\mathbb Z[x]$. It is published separately only so that the per-row certificates, which need $T_u$ for $u$ up to $44$, can start the recurrence from here and stay within the verifier's time limit. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 23, §4.4 (the integer Chebyshev polynomials of the fixed rows), T_24

import Mathlib
import Definitions.Def_OAICatalanChebyshevData

namespace OAI.InternalCatalan

open Polynomial

theorem fixed_chebyshevT_typed_24 :
    Chebyshev.T ℤ 24 = fixedChebyshevTData_24 := by
  sorry

end OAI.InternalCatalan
