-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_6_5
-- name    : GenCountSampleLLL.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:51.259093+00:00
-- url     : https://prove2.me/theorems/6bb89018-816a-40aa-b586-6d45b0ac6996
-- title:
--   Lemma 6.5, p.24 — $\sum_{X\notin\{\mathsf O(\sigma)\}}w(X)\le(1+2mx_a)Z_-$
-- statement:
--   Assume (1.1) with $c=1/100$ for some $x\in(0,1)^{\mathcal C}$, let $m=|\mathcal C|$ and $a\in\mathcal D\subseteq\mathcal C$, and write $Z_-=Z_{\mathcal D^-}$. The total weight outside the output states of $\mathsf S(\mathcal D,a)$ satisfies
--   $$
--   \sum_{X\in\mathsf S(\mathcal D,a)\setminus\{\mathsf O(\sigma):\sigma\in\mathrm{Good}(\mathcal D)\}}w(X)\le(1+2m\,x_a)Z_-.
--   $$
--
--   This bounds the distance of $\pi$ from $\mu^+$ and the cost of the list operations.
--
--   Differences from the source:
--   - encoding: the standing assumption of §2, p.7: "Throughout the proof, we assume (1.1) with c = 1/100", with x ∈ (0,1)^𝒞 → explicit hypotheses `hx : ∀ b, 0 < x b ∧ x b < 1` and `hLLL : I.LLLCond (1/100) x`; reason: the statement on the page omits the section's standing assumption; the Lean states it
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Lemma 6.5, p.24

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees
import Definitions.Def_GenCountSampleLLL_insertionChain

set_option autoImplicit false

open scoped BigOperators ENNReal

open Classical

namespace GenCountSampleLLL

open Inst

/-- Lemma 6.5, p.24 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)), under (1.1) with `c = 1/100`. For `a ∈ D ⊆ C`, the
total weight outside the output states satisfies
`Σ_{X ∈ S(D,a) ∖ {O(σ) : σ ∈ Good(D)}} w(X) ≤ (1 + 2m x_a) Z₋`, with `Z₋ = Z_{D⁻}`.

**Formalization Note.** `m = |C|` is the global number of constraints. -/
theorem lemma_6_5 (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) :
    ∑ X ∈ Finset.univ.filter (fun X : I.S D a => ¬ I.isOut X.1), I.w D a X ≤
      (1 + 2 * (I.m : ℝ) * x a) * I.Z (D.erase a) := by sorry

end GenCountSampleLLL
