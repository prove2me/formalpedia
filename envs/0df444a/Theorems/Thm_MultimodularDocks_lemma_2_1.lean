-- Prove2me | Theorems.Thm_MultimodularDocks_lemma_2_1
-- name    : MultimodularDocks.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:35.892741+00:00
-- url     : https://prove2.me/theorems/8d4bb7a4-6025-4e4b-ae92-177d5644c159
-- title:
--   Lemma 2.1 (corrected: multimodular on the quadrant) — the station UDF $c_i$ is multimodular
-- statement:
--   Let $p$ be a demand profile, i.e. a probability distribution over finite arrival sequences, and let $\eta\ge 0$ be the weight of a stock-out at an empty station. Suppose that the expected cost
--
--   $$
--   c_i(d,b)=\mathbb E_{X\sim p}\bigl[c_X(d,b)\bigr]
--   $$
--
--   is finite for all $d,b\ge 0$. Then $c_i$ is multimodular: inequalities (1)–(3) of Definition 1 hold wherever all their arguments are nonnegative.
--
--   This is the structural property that the whole algorithmic analysis rests on: each station's expected number of dissatisfied customers has diminishing returns in empty and full docks.
--
--   Differences from the source:
--   - correction: Lemma 2.1: c_i (= ∞ off its band, ∞ − ∞ = ∞) satisfies (1)–(3) for all d, b ∈ ℤ → the real expected UDF satisfies (1)–(3) whenever all arguments are ≥ 0; reason: the printed claim is false: X empty, l = 0, u = 2, so c_i = 0 on its band; (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞ (paper.md item 1); App. B.1 calls such cases vacuous, which the convention does not give
--   - generalization: unweighted UDF (η = 1) → weight η ≥ 0 on stock-outs at empty stations; reason: App. B.1 proves the weighted form; η = 1 is the printed lemma
--   - reading: p.39: 'the first term is multiplied by η' → η multiplies the rentals at an empty station (X_t = −1, δ = d + b); reason: the proof (pp.39–40) penalizes 'a stock-out … η ≥ 0 if the station is empty'; the first term counts returns at a full station; the two forms are exchanged by d ↔ b, X ↔ −X (paper.md item 15)
--   - encoding: c_i = E_{X∼p_i}[c_X] finite on its domain → p : PMF (List Arrival), c_i = Σ' X, p(X)·c_X, with Summable assumed at every d, b ≥ 0; reason: Lean's tsum of a non-summable family is 0; the hypothesis is the page's finiteness of c_i (paper.md item 10)
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Lemma 2.1, p.11; proof App. B.1, pp.38–41 (weighted case)

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_stationUDF

namespace MultimodularDocks

/-- **Lemma 2.1** (Freund, Henderson, Shmoys, *Minimizing Multimodular Functions and Allocating
Capacity in Bike-Sharing Systems*, arXiv:1611.09304v5, Lemma 2.1, p.11; proof App. B.1,
pp.38–41, weighted form). For every demand profile `p` on arrival sequences and every weight
`η ≥ 0` of a stock-out at an empty station, the station UDF `c_i(d, b) = E_{X∼p}[c_X(d, b)]` is
multimodular, provided the expectation is finite at every `d, b ≥ 0`.

**Formalization Note** Multimodularity is on the quadrant (`IsMultimodular`; the page's
`∞ − ∞ = ∞` convention makes the printed lemma false at `d = −1`). Finiteness of `c_i` is
`Summable`, since `tsum` of a non-summable family is `0` in Lean. `η = 1` is the printed
(unweighted) lemma. -/
theorem lemma_2_1 (p : PMF (List Arrival)) (η : ℝ) (hη : 0 ≤ η)
    (hsum : ∀ d b : ℤ, 0 ≤ d → 0 ≤ b → Summable fun X => (p X).toReal * udf η d b X) :
    IsMultimodular (stationUDF p η) := by sorry

end MultimodularDocks
