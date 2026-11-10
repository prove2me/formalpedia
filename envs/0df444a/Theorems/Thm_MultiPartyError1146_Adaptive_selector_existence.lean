-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_selector_existence
-- name    : MultiPartyError1146.Adaptive.selector_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:33:47.167617+00:00
-- url     : https://prove2.me/theorems/0072f642-2a7e-463f-a22b-b175bce6c892
-- title:
--   Lemma 3.1 — singleton-isolating set systems
-- statement:
--   Fix any polynomial degree $d\ge1$. There is a constant $A>0$, chosen before the sizes, such that for every positive $n,q$ with $A n\log(2n)\le q\le n^d$, a family of $q$ subsets of $[n]$ has each size at most $\sqrt n$ and satisfies
--   $$|\{t:S^{(t)}\cap U=\{i\}\}|\ge q/(10\sqrt n)$$
--   for every $U\subseteq[n]$ of size at most $\sqrt n$ and every $i\in U$. This supplies the selector family used in phase 3.
--
--   Differences from the source:
--   - encoding: sufficiently large m with Ω(n log n)≤m≤poly(n) → a degree d is fixed first and one uniform lower coefficient A is chosen before all n,q; reason: the polynomial range and asymptotic constant are exposed; q avoids confusing family size with input length
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 3.1, printed p.17, PDF p.19

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Codes

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem selector_existence :
    ∀ d : ℕ, 1 ≤ d → ∃ A : ℝ, 0 < A ∧
      ∀ n q : ℕ, 1 ≤ n → 1 ≤ q →
        A * n * Real.log (2 * n) ≤ (q : ℝ) → (q : ℝ) ≤ (n : ℝ) ^ d →
        ∃ S : Selector n q, IsSelector S := by sorry

end MultiPartyError1146.Adaptive
