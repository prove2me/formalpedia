-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_lemma_2_16
-- name    : ListHashFurstenberg.Main.lemma_2_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:40.195392+00:00
-- url     : https://prove2.me/theorems/00e6135f-a437-4241-9bdb-beee9ddd9ae2
-- title:
--   Lemma 2.16 — amplifying the direction density by random rotations
-- statement:
--   Throughout, $F$ is a finite field with $q=|F|$ elements and $F^n$ is the space of length-$n$ vectors over $F$. A set $S\subseteq F^n$ is **$(\delta,n,r,T)$-Furstenberg** if for at least a $\delta$-fraction of all $r$-dimensional linear subspaces $V\le F^n$ there is a shift $x\in F^n$ with $|(x+V)\cap S|\ge T$.
--
--   Let $0<\varepsilon<\delta<1$ and let $S\subseteq F^n$ be $(\varepsilon,n,r,T)$-Furstenberg. Then there is a $(\delta,n,r,T)$-Furstenberg set $S'\subseteq F^n$ with
--
--   $$|S'|\le\left\lceil\frac{\log(1-\delta)}{\log(1-\varepsilon)}\right\rceil\cdot|S|.$$
--
--   Taking unions of a few images of $S$ under invertible linear maps covers more directions at a controlled cost in size; Corollary 2.17 uses this to move the dependence on $\delta$ out of the exponential.
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ with $q$ a prime power → an arbitrary finite field $F$ with $q=|F|$; reason: every finite field has prime-power order and every prime power is the order of a finite field, so the instances are the same.
--   - encoding: $\log$ with unspecified base → natural logarithm; reason: only the ratio of two logarithms occurs.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Lemma 2.16, p.17

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_Furstenberg

namespace ListHashFurstenberg.Main

/-- Lemma 2.16, p.17 of Kumar–Mon, STOC 2027 submission #1578 (random rotations). Let
`0 < ε < δ < 1` and let `S ⊆ F^n` be `(ε, n, r, T)`-Furstenberg. Then there is a
`(δ, n, r, T)`-Furstenberg set `S' ⊆ F^n` with `|S'| ≤ ⌈log(1-δ) / log(1-ε)⌉ · |S|`. -/
theorem lemma_2_16 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n r : ℕ) (T ε δ : ℝ) (hε : 0 < ε) (hεδ : ε < δ) (hδ : δ < 1)
    (S : Finset (Fin n → F)) (hS : IsFurstenberg ε n r T S) :
    ∃ S' : Finset (Fin n → F), IsFurstenberg δ n r T S' ∧
      (S'.card : ℝ) ≤ (⌈Real.log (1 - δ) / Real.log (1 - ε)⌉ : ℝ) * S.card := by sorry

end ListHashFurstenberg.Main
