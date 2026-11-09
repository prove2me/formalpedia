-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_removal_of_right_cofactor
-- name    : NCFactorClosure607.Circuits.removal_of_right_cofactor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:22.995262+00:00
-- url     : https://prove2.me/theorems/edf5e970-8c28-4f3c-9a7a-09d34537f49b
-- title:
--   Theorem 3.1: the automaton map removes a right cofactor, $T(gh)=g$
-- statement:
--   Let $h\in F\langle X\rangle$ be nonzero of degree $b\ge1$, choose a word $v=v_1\cdots v_b$ with $c=[v]h\neq0$, let $d_\ell=[v_{\ell+1}\cdots v_b]h$ for $1\le\ell\le b$, and let $T$ be the weighted-automaton map defined from these data. Then for every word $r\in X^*$,
--   $$T(rh)=r,$$
--   and consequently, for every polynomial $g\in F\langle X\rangle$,
--   $$T(gh)=g .$$
--
--   The map $T$ depends only on the cofactor $h$, not on the polynomial multiplied on its left; this is what makes it applicable to a circuit for $f=gh$ in which $g$ is unknown.
--
--   **Formalization Note** The hypotheses are `1 ≤ data.b` and `data.ValidFor h`, which contains $h\neq0$, $|v|=\deg h$, $c=[v]h\neq0$ and the suffix coefficients. The monomial of $r$ is `wordPoly r`.
--
--   Differences from the source:
--   - generalization: $X=\{x_1,\dots,x_m\}$ with $m\ge1$ → an arbitrary type `X`; reason: the statement for every type specializes to every finite nonempty variable set.
--   - encoding: the restatement "equivalently, $[u]T(gh)=[u]g$ for every word $u$" → not a separate clause; reason: it is equivalent to $T(gh)=g$ because a polynomial is determined by its coefficients.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.7, Theorem 3.1, with the setup of §3, eq. (2), p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_CofactorNFA

namespace NCFactorClosure607.Circuits

/-- Theorem 3.1 (p.7), with the standing setup of §3 (p.6): let `h ≠ 0` have degree `b ≥ 1`
and let `data` be cofactor data for `h` (a word `v` of length `b` with `c = [v]h ≠ 0` and the
coefficients of its proper suffixes). Then the automaton map `T` satisfies `T(rh) = r` for every
word `r`, and consequently `T(gh) = g` for every polynomial `g`. -/
theorem removal_of_right_cofactor {F : Type*} [Field F] {X : Type*}
    (h : FreeAlgebra F X) (data : CofactorData F X) (hb : 1 ≤ data.b)
    (hdata : data.ValidFor h) :
    (∀ r : FreeMonoid X, data.cofactorMap (wordPoly r * h) = wordPoly r) ∧
      ∀ g : FreeAlgebra F X, data.cofactorMap (g * h) = g := by sorry

end NCFactorClosure607.Circuits
