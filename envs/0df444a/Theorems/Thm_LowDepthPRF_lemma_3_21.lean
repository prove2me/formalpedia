-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_3_21
-- name    : LowDepthPRF.lemma_3_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:27.84678+00:00
-- url     : https://prove2.me/theorems/522a8f56-41c3-456a-909b-04a449d647a1
-- title:
--   Lemma 3.21 — sum amplifies almost-randomness (corrected: $n\ge1$)
-- statement:
--   Let $n\ge1$. If $F=\{F_{r,aux}:X\to\{0,1\}^b\}$ is $(q,\epsilon)$-almost-random, then
--
--   $$F^{\oplus n}\ \text{is}\ (q,\epsilon^n)\text{-almost-random}.$$
--
--   XOR of $m=\lambda$ independent trees drives the bad-event probability of Lemma 4.10 from $1/2$ to $2^{-m}$.
--
--   Differences from the source:
--   - correction: every n ∈ ℕ → n ≥ 1; reason: at n = 0, F^{⊕0} is the constant-0 family and ε⁰ = 1; F_{r,aux}(x) = r with R = {0,1}^b (b ≥ 1), one aux and BAD = ∅ is (1, 1/2)-almost-random, but for F^{⊕0} every singleton must lie in BAD, so Pr = 1 is not < 1
--   - encoding: key space (R × AUX)^n of F^{⊕n} → R^n × AUX^n; reason: the regrouping of the paper's proof (A.1)
--   - encoding: Y → Y = {0,1}^b; reason: Def 3.8 defines sums for Y = {0,1}^b
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 3.21, p.15 (pdf 17); proof in A.1, p.36 (pdf 38)

import Mathlib
import Definitions.Def_LowDepthPRF_AlmostRandom

namespace LowDepthPRF

/-- **Lemma 3.21 (Sum Amplifies Almost-Randomness)** (Ding, Jain, Komargodski, arXiv:2608.25213,
sha256 89a55849…, p.15; proof in A.1, p.36). Let `n ∈ ℕ`. If `F : X → Y` is `(q, ε)`-almost-random,
then `F^{⊕n} : X → Y` is `(q, ε^n)`-almost-random.

**Formalization Note.** Correction `1 ≤ n`: for `n = 0`, `F^{⊕0}` is the constant-`0` family and
`ε⁰ = 1`; with `q ≥ 1`, `b ≥ 1` and e.g. `F_{r,aux}(x) = r` (`R = {0,1}^b`, a single `aux`, any `X`,
`BAD = ∅`), which is `(q, 1/2)`-almost-random, every singleton `x` must lie in `BAD` for `F^{⊕0}`
(its output is not uniform), so `Pr[(x, aux) ∈ BAD] = 1` is not `< 1`. The key of `F^{⊕n}`,
`(R × AUX)^n`, is regrouped as `R^n × AUX^n` (`sumAR`). -/
theorem lemma_3_21 {R AUX X : Type} [Fintype R] [Fintype AUX] {b : ℕ}
    (F : R → AUX → X → (Fin b → Bool)) (q n : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hF : AlmostRandom F q ε) : AlmostRandom (sumAR F n) q (ε ^ n) := by sorry

end LowDepthPRF
