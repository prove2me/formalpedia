-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_3_12
-- name    : LowDepthPRF.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:47.629202+00:00
-- url     : https://prove2.me/theorems/c0fc53a5-998c-405f-a422-9f45b7d5bbab
-- title:
--   Lemma 3.12 — output restriction preserves pseudorandomness
-- statement:
--   Let $\mathrm{type}\in\{\text{strong},\text{weak}\}$ and let $F=\{F_k:\{0,1\}^a\to\{0,1\}^b\}_{k\in K}$ be $(q,t,\epsilon)$-type pseudorandom. Then for every $b'\le b$ the family $F'_k(x):=(F_k(x))_{1\dots b'}$ of the first $b'$ output bits is
--
--   $$(q,t,\epsilon)\text{-type pseudorandom}.$$
--
--   There is no loss in size. This is the step that restricts the hash's range to its first $c_q$ blocks in Lemma 4.10.
--
--   Differences from the source:
--   - generalization: restriction of Y^n to its first m′ blocks, m′ ≤ n → restriction of b output bits to the first b′ ≤ b bits; reason: with Y = {0,1}^c, Y^n is n·c bits in block order, so the case b = n·c, b′ = m′·c is the printed statement
--   - generalization: t ∈ ℕ → t real; reason: size ≤ t for real t is size ≤ ⌊t⌋
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 3.12, p.13 (pdf 15)

import Mathlib
import Definitions.Def_LowDepthPRF_Pseudorandom

namespace LowDepthPRF

/-- **Lemma 3.12 (Output Restriction Preserves Pseudorandomness)** (Ding, Jain, Komargodski,
arXiv:2608.25213, sha256 89a55849…, p.13). Let `type ∈ {strong, weak}`. Let
`F = {F_k : X → Y^n}` be `(q, t, ε)`-type pseudorandom. Then for any `m′ ≤ n`,
`F′ = {F′_k : X → Y^{m′}}` is `(q, t, ε)`-type pseudorandom, where
`F′_k(x) := (F_k(x))_{1…m′}`.

**Formalization Note.** Stated for keeping the first `b′` of `b` output bits, any `b′ ≤ b`. With
`Y = {0,1}^c`, `Y^n` is `n·c` bits with the blocks in order, so keeping the first `m′` blocks is
the case `b = n·c`, `b′ = m′·c`. The key space is any nonempty finite type. -/
theorem lemma_3_12 {K : Type} [Fintype K] [Nonempty K] (ty : PRType) {a b : ℕ} (F : FunFam K a b)
    (q : ℕ) (t ε : ℝ) (b' : ℕ) (hb : b' ≤ b) (hF : TypePR ty F q t ε) :
    TypePR ty (restrictFam F b' hb) q t ε := by sorry

end LowDepthPRF
