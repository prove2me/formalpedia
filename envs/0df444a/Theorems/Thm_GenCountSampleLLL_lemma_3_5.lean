-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_3_5
-- name    : GenCountSampleLLL.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:55:43.351118+00:00
-- url     : https://prove2.me/theorems/a54e2995-9c20-4621-b06a-4347bcf3d516
-- title:
--   Lemma 3.5, p.16 — Algorithm 1 makes at most $1+mx_a$ calls in expectation
-- statement:
--   Assume (1.1) with $c=1/100$ for some $x\in(0,1)^{\mathcal C}$, and let $m=|\mathcal C|$. For every $a\in\mathcal D\subseteq\mathcal C$, the expected total number of calls to the marginal estimator (Algorithm 1) in computing $\hat r_{\mathcal D,a}$, including the initial call, is at most
--   $$
--   1+m\,x_a.
--   $$
--
--   With the polynomial work per call, this gives the polynomial expected running time of the estimator.
--
--   Differences from the source:
--   - encoding: the standing assumption of §2, p.7: "Throughout the proof, we assume (1.1) with c = 1/100", with x ∈ (0,1)^𝒞 → explicit hypotheses `hx : ∀ b, 0 < x b ∧ x b < 1` and `hLLL : I.LLLCond (1/100) x`; reason: the statement on the page omits the section's standing assumption; the Lean states it
--   - encoding: "the expected total number of calls … in computing r̂_{𝒟,a}" → the expectation in [0, ∞] of the call count under `estLaw D a`, the law of Algorithm 1; reason: Algorithm 1 is the paper's estimator; an extended-real expectation has no junk value
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Lemma 3.5, p.16

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees
import Definitions.Def_GenCountSampleLLL_estLaw

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

open Inst

/-- Lemma 3.5, p.16 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)), under (1.1) with `c = 1/100`.
For every `a ∈ D ⊆ C`, the expected total number of calls to the marginal estimator
(Algorithm 1) in computing `r̂_{D,a}`, including the initial call, is at most `1 + m x_a`.

**Formalization Note.** `estLaw D a` is the joint law of Algorithm 1's output and its total call
count; the expectation is in `ℝ≥0∞`, so it is not a junk value. `m = |C|` is the global number of
constraints. -/
theorem lemma_3_5 (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) :
    ∑' vn : ℤ × ℕ, I.estLaw D a vn * (vn.2 : ℝ≥0∞) ≤
      ENNReal.ofReal (1 + (I.m : ℝ) * x a) := by sorry

end GenCountSampleLLL
