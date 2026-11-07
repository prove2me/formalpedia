-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_3_22
-- name    : LowDepthPRF.lemma_3_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:55.767264+00:00
-- url     : https://prove2.me/theorems/0f369429-0dea-4451-aaed-bc4f7693ced3
-- title:
--   Lemma 3.22 — almost-random implies $(q,\infty,\epsilon)$-strong pseudorandom (Lemma 3.2 of [BHKN13, BHKN19])
-- statement:
--   Let $F=\{F_{r,aux}:\{0,1\}^a\to\{0,1\}^b\}$ with key space $R\times AUX$ ($R$, $AUX$ finite and nonempty). If $F$ is $(q,\epsilon)$-almost-random, then $F$ is
--
--   $$(q,\infty,\epsilon)\text{-strong pseudorandom}:$$
--
--   every adversary of any size making at most $q$ queries, possibly adaptive and possibly repeated, distinguishes $F$ from a random function with advantage less than $\epsilon$.
--
--   This is the bridge from the non-adaptive analysis of §4 to adaptive security. It is cited from Berman–Haitner–Komargodski–Naor.
--
--   Differences from the source:
--   - encoding: families X → Y → X = {0,1}^a, Y = {0,1}^b; reason: the adversary's oracle gates read and write bit strings; the paper applies the lemma to such families
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 3.22, p.15 (pdf 17), citing [BHKN13, BHKN19, Lemma 3.2]

import Mathlib
import Definitions.Def_LowDepthPRF_AlmostRandom

namespace LowDepthPRF

/-- **Lemma 3.22 (Almost-Random ⇒ Strong Pseudorandom; Lemma 3.2 of [BHKN13, BHKN19])** (Ding,
Jain, Komargodski, arXiv:2608.25213, sha256 89a55849…, p.15). If `F` is `(q, ε)`-almost-random,
then `F` is `(q, ∞, ε)`-strong pseudorandom.

**Formalization Note.** `(q, ∞, ε)` quantifies over adversaries of every size; they may choose
queries adaptively and repeat them. Inputs and outputs are bit strings `X = {0,1}^a`,
`Y = {0,1}^b`, so that the adversary's oracle gates can read and write them; the family with key
space `R × AUX` is viewed as a `FunFam (R × AUX) a b`. -/
theorem lemma_3_22 {R AUX : Type} [Fintype R] [Nonempty R] [Fintype AUX] [Nonempty AUX] {a b : ℕ}
    (F : R → AUX → (Fin a → Bool) → (Fin b → Bool)) (q : ℕ) (ε : ℝ)
    (hF : AlmostRandom F q ε) : StrongPRAll (fun k : R × AUX => F k.1 k.2) q ε := by sorry

end LowDepthPRF
