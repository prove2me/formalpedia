-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_3_11
-- name    : LowDepthPRF.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:39.634206+00:00
-- url     : https://prove2.me/theorems/1706c76c-3840-484f-bd42-56c10cd4992b
-- title:
--   Lemma 3.11 — product preserves pseudorandomness (corrected: $n\ge1$ for the security clause)
-- statement:
--   There is a universal constant $C>0$ such that the following holds, with $\rho(q,n,s,a,b)=Cnq^2(s+a+b+1)$. Let $\mathrm{type}\in\{\text{strong},\text{weak}\}$, and let $F:\{0,1\}^a\to\{0,1\}^b$, with keys in $\{0,1\}^{\ell}$, be an $(s,d)$-function family that is $(q,t,\epsilon)$-type pseudorandom, with $t-\rho(q,n,s,a,b)>0$. Then:
--
--   1. $F^{\times n}:\{0,1\}^a\to(\{0,1\}^b)^n$ is an $(ns,d)$-function family;
--   2. if $n\ge1$, $F^{\times n}$ is $\bigl(q,\ t-\rho(q,n,s,a,b),\ n\epsilon\bigr)$-type pseudorandom.
--
--   The product extends the output length at a linear loss in security. The proof of Lemma 4.9 uses it with $q$ keys and $\Delta$ samples.
--
--   Differences from the source:
--   - correction: the security clause for every n ∈ ℕ → only for n ≥ 1; reason: at n = 0, F^{×0} has no output bits, every adversary has advantage 0, and 'advantage less than 0·ε = 0' fails: e.g. the truth-table family (key = all functions {0,1}^a → {0,1}^b as bits) is (q, t, ε)-strong pseudorandom for any ε > 0, and with t ≥ 1 a one-gate adversary exists
--   - encoding: a sufficiently large universal constant C > 0 → ∃ C > 0, quantified before every other variable; reason: the meaning of 'universal'
--   - encoding: Y^n and the key space K^n → n·b and n·kl bits, block i at positions i·b, …; reason: binary encoding lengths, as the lemma names them
--   - generalization: t ∈ ℕ → t real; reason: size ≤ t for real t is size ≤ ⌊t⌋
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 3.11, p.13 (pdf 15), with ρ defined on p.13

import Mathlib
import Definitions.Def_LowDepthPRF_Pseudorandom

namespace LowDepthPRF

/-- **Lemma 3.11 (Product Preserves Pseudorandomness)** (Ding, Jain, Komargodski,
arXiv:2608.25213, sha256 89a55849…, p.13). With `ρ(q, n, s, a, b) = C n q² (s + a + b + 1)` for a
sufficiently large universal constant `C > 0`: let `type ∈ {strong, weak}` and let `a`, `b` be the
binary encoding lengths of `X` and `Y`. If the `(s, d)`-function family `F : X → Y` is
`(q, t, ε)`-type pseudorandom, then `F^{×n} : X → Y^n` is an `(ns, d)`-function family that is
`(q, t − ρ(q, n, s, a, b), nε)`-type pseudorandom, whenever the stated circuit-size bound is
positive.

**Formalization Note.** `C` is existential and comes first. `Y^n` and the key `K^n` are encoded
as `n·b` and `n·kl` bits (`prodFam`). The pseudorandomness clause carries the correction
`1 ≤ n`: for `n = 0`, `F^{×0}` has no output bits, every adversary has advantage `0`, and
"advantage less than `0·ε = 0`" fails for any adversary of size `≤ t` (e.g. a one-gate circuit
when `t ≥ 1`, with `F` a truly random function family), so the printed clause is false at
`n = 0`. -/
theorem lemma_3_11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ty : PRType) (kl a b n s d q : ℕ) (t ε : ℝ) (F : FunFam (Fin kl → Bool) a b),
        IsSizeDepth F s d →
        TypePR ty F q t ε →
        0 < t - C * n * (q : ℝ) ^ 2 * (s + a + b + 1) →
        IsSizeDepth (prodFam F n) (n * s) d ∧
          (1 ≤ n → TypePR ty (prodFam F n) q (t - C * n * (q : ℝ) ^ 2 * (s + a + b + 1))
            (n * ε)) := by sorry

end LowDepthPRF
