-- Prove2me | Theorems.Thm_NadlerCLS_pnSearch_check_P
-- name    : NadlerCLS.pnSearch_check_P
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:01:22.803877+00:00
-- url     : https://prove2.me/theorems/1ad12692-b303-4f96-beed-338d90c5daf0
-- title:
--   Answers of $\beta$-Projected-Nadler are verifiable in polynomial time
-- statement:
--   Answers of $\beta$-Projected-Nadler can be verified in polynomial time.
--
--   Fix a dimension $n$, a rational exponent $\beta\in(0,1]$ and a natural number $k$. Consider the search problem $\beta$-Projected-Nadler on $X=[0,1]^n$ with only the numerical promise (instances: a projection circuit $\Pi$, a metric circuit $d$, and rationals $\varepsilon_1,\varepsilon_2,L_P,L_d,D>0$, $k_{\mathrm{c}}\in(0,1)$ with $\varepsilon_2<\varepsilon_1(1-k_{\mathrm{c}})$; answers: the outputs (N1)–(N4) of Definition 1), and restrict its answers to strings $t$ of length
--
--   $$|t|\le (|s|+1)^k+k,$$
--
--   where $s$ is the binary code of the instance. Then the checking language
--
--   $$L=\{\,s\#t \;:\; s \text{ is the code of a valid instance and } t \text{ is an answer of length at most } (|s|+1)^k+k\,\}$$
--
--   is in $\mathrm{P}$: some one-tape Turing machine decides membership of $s\#t$ in $L$ within a polynomial number of steps.
--
--   This is the verification half of the statement that $\beta$-Projected-Nadler belongs to TFNP, needed for its CLS-membership (Theorem 3.2): checking an answer amounts to parsing the instance, checking well-behavedness and the numerical promise, evaluating the circuits $\Pi$ and $d$ exactly at the rational witness points, and comparing rationals (for (N3), comparing $\|P(x)-P(y)\|_1/L_P$ with $\|x-y\|_1^{\beta}$ by raising both sides to the denominator of the fixed $\beta$).
--
--   **Formalization Note** The problem is the public `bounded (pnSearch n β) k`, its checking language is Cook's `checkLang` over the alphabet `Option (Bool ⊕ Bool)` (separator `none`), and $\mathrm{P}$ is Cook's class `CookPvsNP.P` on one-tape Turing machines.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101v4 (3 Nov 2026), Section 3, Remark 3.1, p.9 ("The numerical promise 0 < ε2 < ε1(1 − k) can be checked in polynomial time") and p.9 ("An output of type (N2) can be checked in polynomial time by evaluating Π and d at the rational witness points"); membership in TFNP as used for Theorem 3.2, p.11, and the proof of Lemma C.6, p.38 ("respects the polynomial witness size").

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_pnSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

theorem pnSearch_check_P (n : ℕ) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (k : ℕ) :
    CookPvsNP.checkLang (fun x y => (bounded (pnSearch n β) k).valid x ∧
      (bounded (pnSearch n β) k).answer x y) ∈ CookPvsNP.P (Option (Bool ⊕ Bool)) := by sorry

end NadlerCLS
