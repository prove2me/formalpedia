-- Prove2me | Theorems.Thm_LocalLLL_Main_lemma_2_1
-- name    : LocalLLL.Main.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:24.749779+00:00
-- url     : https://prove2.me/theorems/7d07fadd-1995-4fc7-b3d0-8449cb81bbb3
-- title:
--   Lemma 2.1 — ruling sets under bounded local independence
-- statement:
--   For a finite graph $H$ with at most $n\ge1$ vertices, suppose every independent subset of every radius-four ball has at most $k$ members. There is a uniform randomized LOCAL algorithm outputting an independent 2-ruling set $S$ with
--
--   $$T\le A\bigl(\log(k+2)+\ell(n)\bigr)^B,\qquad \Pr[\text{failure}]\le n^{-a},\quad\ell(n)=\log\log(n+16).$$
--
--   The exponent $B$ is absolute. For every $a>0$, the positive constant $A$ is uniform over $n,k,H$ and identifiers. The program may know $n,k,a$ but sees the graph through messages only. This is the symmetry-breaking result used for danger centers.
--
--   Differences from the source:
--   - reading: poly(log log n) with any desired constant failure exponent → one polynomial exponent B before the failure exponent; reason: Reading R: §3.3 changes only multiplicative constants with the failure exponent; the evidence and remaining cited-algorithm burden are recorded in MODERATION_NOTES.md
--   - generalization: unique identifiers in the usual LOCAL model → arbitrary injective natural identifiers, without a polynomial size bound; reason: random short identifiers can be generated with sufficiently small collision probability; the theorem specializes to bounded identifiers
--   - encoding: finite graph distances, balls, powers and cardinalities → finite vertex types, extended distance and natural neighbor-set cardinalities; reason: disconnected pairs have infinite distance and graph powers remain loopless; cardinalities agree on finite graphs
--   - encoding: poly(log log n) asymptotic round complexity → T ≤ A·(log log(n+16))^B for every n ≥ 1; reason: padding preserves the asymptotic class and defines the expression positively at small n; n is a common size upper bound
--   - encoding: success probability at least 1−n^(−a) → outer measure of the failure set at most n^(−a); reason: an upper bound on failure remains meaningful without imposing measurability of arbitrary local computation
--   - encoding: arbitrarily large messages to each neighbor → unrestricted broadcast messages and received-message dictionaries indexed by sender ID; reason: a broadcast may contain one entry per recipient; execution still receives only neighbor messages
--   - generalization: the common size bound n is polynomial in the actual network size in the LOCAL model paragraph → any n ≥ 1 with card V ≤ n, including empty networks and arbitrarily loose upper bounds; reason: the source explicitly permits padding by isolated vertices in §2; padding to n and restricting execution to the original components gives the same guarantee and includes every source instance
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), Lemma 2.1, p. 2 (PDF 3); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Repair

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalLLL.Main

/-- Lemma 2.1, printed p. 2; Appendix A.1, pp. 16–17. -/
theorem lemma_2_1 :
    ∃ B : ℕ, ∀ a : ℝ, 0 < a → ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ,
      ∃ T : ℕ, (T : ℝ) ≤ A * (Real.log ((k : ℝ) + 2) + loglog n) ^ B ∧
      ∃ alg : LocalAlg Unit Bool,
      ∀ (V : Type) [Fintype V] (H : SimpleGraph V) (id : V → ℕ),
        Function.Injective id → Fintype.card V ≤ n → localIndependence H k →
        tapes V {ω | ¬ (independent H {v | run alg T H id (fun _ => ()) ω v = true} ∧
          ruling H 2 {v | run alg T H id (fun _ => ()) ω v = true})} ≤
            ENNReal.ofReal ((n : ℝ) ^ (-a)) := by sorry

end LocalLLL.Main
