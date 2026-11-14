-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_lemma_2_2
-- name    : IntegerRootsFN.Main.lemma_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:45.746715+00:00
-- url     : https://prove2.me/theorems/9ea05891-3bba-4787-b268-0aa449be0d22
-- title:
--   Lemma 2.2 — truncation retains nearby roots
-- statement:
--   Let $n,b\ge1$ be integers and $f(x)=\sum_{j=0}^na_jx^j\in\mathbb Z[x]$ have exact degree $n$, nonzero leading coefficient and $|a_j|<2^b$. Put $d=\min(n,b)$ and $g(x)=a_nx^d+\cdots+a_{n-d}$. If $d<n$, every integer root $r$ of $f$ with $|r|\ge2$ satisfies
--
--   $$\exists\alpha\in\mathbb C:\quad g(\alpha)=0,\qquad |r-\alpha|<2.$$
--
--   The truncation is constructed from the coefficients, not provided as an unrelated polynomial. The restriction on $r$ leaves $-1,0,1$ to be handled separately.
--
--   Differences from the source:
--   - encoding: positive integer parameters and a truncated integer polynomial viewed over C → positive natural parameters and canonical complexification of the coefficient-defined truncation; reason: these denote the same parameters, coefficients and roots without any machine input or output assertion
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 5, Lemma 2.2

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_PolynomialData

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem lemma_2_2 (n b : ℕ) (f : Polynomial ℤ) (hf : Valid f n b)
    (hd : min n b < n) (r : ℤ) (hr : f.IsRoot r) (hrlarge : 2 ≤ |r|) :
    ∃ α : ℂ, (complexify (truncate f n b)).IsRoot α ∧ ‖(r : ℂ) - α‖ < 2 := by sorry

end IntegerRootsFN.Main
