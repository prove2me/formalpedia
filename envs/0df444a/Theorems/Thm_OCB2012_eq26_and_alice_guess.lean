-- Prove2me | Theorems.Thm_OCB2012_eq26_and_alice_guess
-- name    : OCB2012.eq26_and_alice_guess
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-07T23:12:28.270089+00:00
-- url     : https://prove2.me/theorems/93148970-2162-4c2c-b459-58df03a4cb16
-- title:
--   Appendix E, Eq. (26) — Bob's and Alice's guessing probabilities
-- statement:
--   With the process matrix $W$ of Eq. (7), Alice's CJ matrices $\xi(x,a)$ (Eq. (20)) and Bob's $\eta(y,b,b')$ (Eqs. (21)–(23)), for any qubit density matrix $\rho^{B_2}$:
--   1. (Eq. (26)) for all bits $a,b,y$, $$P(y\mid a,b,b'=1)=\sum_x\operatorname{Tr}\big[W(\xi(x,a)\otimes\eta(y,b,1))\big]=\tfrac12\Big[1+\tfrac{(-1)^{y+a}}{\sqrt2}\Big];$$
--   2. with $a,b$ uniform, $$P(x=b\mid b'=0)=\tfrac14\sum_{a,b}\sum_y\operatorname{Tr}\big[W(\xi(b,a)\otimes\eta(y,b,0))\big]=\frac{2+\sqrt2}{4}.$$
--   Both are equalities of complex numbers.
-- source:
--   O. Oreshkov, F. Costa, Č. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, Appendix E, Eq. (26) and the text following Eq. (27)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem eq26_and_alice_guess (ρ : Matrix Qubit Qubit ℂ) (hρ : PeresTerno.IsDensityMatrix ρ) :
    (∀ a b y : Bool, ∑ x : Bool, prob W7 (ξ x a) (η ρ y b true) =
        (((1 / 2 : ℝ) * (1 + (if xor y a then -1 else 1) / Real.sqrt 2) : ℝ) : ℂ)) ∧
    (1 / 4 : ℂ) * ∑ a : Bool, ∑ b : Bool, ∑ y : Bool, prob W7 (ξ b a) (η ρ y b false) =
        (((2 + Real.sqrt 2) / 4 : ℝ) : ℂ) := by sorry

end OCB2012
