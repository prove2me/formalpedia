-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_3_10
-- name    : LowDepthPRF.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:41.406991+00:00
-- url     : https://prove2.me/theorems/9c21e0b2-831b-4977-9855-a9c8bd46c692
-- title:
--   Lemma 3.10 — direct sum lemma
-- statement:
--   There is a universal constant $C>0$ such that the following holds, with $\rho(q,n,s,a,b)=Cnq^2(s+a+b+1)$. Let $\mathrm{type}\in\{\text{strong},\text{weak}\}$, and let $F_1,\dots,F_n$ be families $\{0,1\}^a\to\{0,1\}^b$ (with bit-string keys), each of evaluation size at most $s$. If some $F_i$ is $(q,t,\epsilon)$-type pseudorandom and $t-\rho(q,n,s,a,b)>0$, then
--
--   $$F_1\oplus\cdots\oplus F_n\ \text{is}\ \bigl(q,\ t-\rho(q,n,s,a,b),\ \epsilon\bigr)\text{-type pseudorandom}.$$
--
--   One pseudorandom summand makes the whole sum pseudorandom. Lemma 4.2 uses this to make a WPRF key-uniform.
--
--   Differences from the source:
--   - encoding: a sufficiently large universal constant C > 0 → ∃ C > 0, quantified before every other variable; reason: the meaning of 'universal'
--   - encoding: families {0,1}^a → {0,1}^b with evaluation size s → bit-string keys of lengths kl i (possibly different); reason: evaluation size (Def 3.1) needs the key as circuit input
--   - generalization: t ∈ ℕ → t real; reason: size ≤ t for real t is size ≤ ⌊t⌋
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 3.10, p.13 (pdf 15), with ρ defined on p.13

import Mathlib
import Definitions.Def_LowDepthPRF_Pseudorandom

namespace LowDepthPRF

/-- **Lemma 3.10 (Direct Sum Lemma)** (Ding, Jain, Komargodski, arXiv:2608.25213, sha256 89a55849…,
p.13). With `ρ(q, n, s, a, b) = C n q² (s + a + b + 1)` for a sufficiently large universal
constant `C > 0`: let `type ∈ {strong, weak}` and suppose each `F_i : {0,1}^a → {0,1}^b` has
evaluation size at most `s`. If some `F_i` is `(q, t, ε)`-type pseudorandom, then
`F_1 ⊕ ⋯ ⊕ F_n` is `(q, t − ρ(q, n, s, a, b), ε)`-type pseudorandom, whenever the stated
circuit-size bound is positive.

**Formalization Note.** `C` is existential and comes first, before every other quantity
("universal constant"). The `F_i` may have different key lengths `kl i`; keys are bit strings so
that evaluation size is defined (Definition 3.1). `t` is real. -/
theorem lemma_3_10 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ty : PRType) (n a b : ℕ) (kl : Fin n → ℕ)
        (F : (i : Fin n) → FunFam (Fin (kl i) → Bool) a b) (s q : ℕ) (t ε : ℝ),
        (∀ i, HasEvalSize (F i) s) →
        (∃ i, TypePR ty (F i) q t ε) →
        0 < t - C * n * (q : ℝ) ^ 2 * (s + a + b + 1) →
        TypePR ty (sumFam (K := fun i => Fin (kl i) → Bool) F) q
          (t - C * n * (q : ℝ) ^ 2 * (s + a + b + 1)) ε := by sorry

end LowDepthPRF
