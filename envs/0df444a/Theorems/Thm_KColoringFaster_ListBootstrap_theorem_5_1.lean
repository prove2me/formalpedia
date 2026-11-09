-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_theorem_5_1
-- name    : KColoringFaster.ListBootstrap.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:57.776843+00:00
-- url     : https://prove2.me/theorems/0f728da5-d59c-4fa9-8f4e-023404bbf8b4
-- title:
--   Theorem 5.1 — general bootstrap
-- statement:
--   Fix an integer $k\ge 3$ and a real $a<2$. There is $\varepsilon>0$, depending only on $k$ and $a$, with the following property. If $(k-1)$-list-coloring over arbitrary palettes has a randomized algorithm running in
--   $$O^*(a^n)$$
--   time (deciding list colorability of instances whose lists all have size at most $k-1$, with error at most $e^{-cn}$ on both sides for some $c>0$), then $k$-list-coloring over arbitrary palettes has a randomized algorithm running in
--   $$O^*\big((2-\varepsilon)^n\big)$$
--   time, with one-sided error at most $e^{-n}$.
--
--   Iterating this from list size $3$ up to $k$ gives the main theorem; that the saving $\varepsilon$ depends only on $k$ and $a$ is what makes the iteration possible.
--
--   **Formalization Note** Algorithms and $O^*$ are as in the definition `Algorithms`.
--
--   Differences from the source:
--   - reading: "for some $\varepsilon>0$ depending only on $k, a$" → $\varepsilon$ is chosen before the assumed algorithm (its program, polynomials and error constant); reason: this is what "depending only on $k,a$" means
--   - reading: hypothesis "a randomized algorithm" → error at most $e^{-cn}$ on both sides for some $c>0$; reason: §3 (p. 7) allows exponentially small error for all algorithms; two-sided error is the weakest hypothesis
--   - reading: conclusion "a randomized algorithm" → one-sided error at most $e^{-n}$; reason: the bound the proof prints (p. 25, "The probability of missing a coloring is at most $e^{-n}$" and "Every acceptance is sound")
--   - encoding: $O^*(\cdot)$ time → one program and polynomials $p,q$ fixed before the input, worst-case cost $\lceil p(\sigma)\,T\rceil$ on the integer RAM with registers of at most $q(\sigma)$ bits; reason: unit cost with polynomially bounded registers equals bit cost up to polynomial factors
--   - encoding: arbitrary palettes → colors in $\mathbb N$; reason: any finite palette is numbered
--   - generalization: nonempty lists → lists may be empty; reason: Algorithm 3 rejects an empty list immediately (p. 26), and the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 22, Theorem 5.1

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Algorithms

open Classical

namespace KColoringFaster.ListBootstrap

/-- Theorem 5.1 (General bootstrap), p. 22. Fix an integer `k ≥ 3` and `a < 2`. There is `ε > 0`,
depending only on `k` and `a`, such that: if `(k-1)`-list-coloring over arbitrary palettes has a
randomized algorithm running in `O*(a^n)` time (error at most `e^{-c n}` on both sides for some
`c > 0`), then k-list-coloring over arbitrary palettes has a randomized algorithm running in
`O*((2 - ε)^n)` time, with one-sided error at most `e^{-n}`. -/
theorem theorem_5_1 (k : ℕ) (hk : 3 ≤ k) (a : ℝ) (ha : a < 2) :
    ∃ ε : ℝ, 0 < ε ∧
      ((∃ c : ℝ, 0 < c ∧ RandDecides encList ListInstance.n (MaxListLE (k - 1)) ListColorable
          (fun I => a ^ I.n) (expErr c) (expErr c)) →
        RandDecides encList ListInstance.n (MaxListLE k) ListColorable
          (fun I => (2 - ε) ^ I.n) (expErr 1) zeroErr) := by sorry

end KColoringFaster.ListBootstrap
