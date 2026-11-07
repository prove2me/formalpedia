-- Prove2me | Theorems.Thm_MemoryRegret_lemma_6_1_bayes_block
-- name    : MemoryRegret.lemma_6_1_bayes_block
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:26.267331+00:00
-- url     : https://prove2.me/theorems/1881d99a-6fbc-4a46-97d9-7b9f20e2c537
-- title:
--   Lemma 6.1 — one block: Bayes-optimal mistakes
-- statement:
--   Let $0<\epsilon\le\frac12$. Let $Y^*$ be a fair bit and, conditionally on $Y^*$, let $Y_1,\dots,Y_m$ be independent with $Y_i\sim\mathrm{Ber}(Y^*,\frac12+\epsilon)$. If $M^*$ is the number of mistakes of the Bayes-optimal online predictor over the $m$ rounds, then
--   $$\mathbb E[M^*]\ge\frac m2-2\epsilon^2m^{3/2}.$$
--
--   Correlated labels within a block therefore help an online predictor only a little, which is the key to the NO case of the reduction from distinguishing to online learning.
--
--   Differences from the source:
--   - encoding: ϵ > 0 → 0 < ϵ ≤ ½; reason: Ber(Y*, ½ + ϵ) is a distribution only for ϵ ≤ ½; this excludes only undefined cases. The printed proof uses ϵ ≤ ¼, but the statement is kept on all of (0, ½]
--   - encoding: E[M*] of the Bayes-optimal predictor → bayesMistakes of the law of (Y_1, …, Y_m); reason: the predictor errs with the smaller of the two next-label probabilities, so the two quantities are equal
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Lemma 6.1, p.34

import Mathlib
import Definitions.Def_MemoryRegret_berBlock
import Definitions.Def_MemoryRegret_bayesMistakes

namespace MemoryRegret

/-- **Lemma 6.1 (one block: the Bayes-optimal predictor makes nearly `m/2` mistakes).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Lemma 6.1, p.34.

Let `0 < ϵ ≤ ½`, `Y* ∈_R {0,1}` and, given `Y*`, `Y_1, …, Y_m` i.i.d. `Ber(Y*, ½ + ϵ)`; the law
of `(Y_1, …, Y_m)` is `blockLabelLaw ϵ`. The expected number of mistakes of the Bayes-optimal
online predictor satisfies `E[M*] ≥ m/2 − 2ϵ²m^{3/2}`.

**Formalization Note.** `E[M*]` is `bayesMistakes`. The paper says `ϵ > 0`; `Ber(Y*, ½ + ϵ)` is
a distribution only for `ϵ ≤ ½`, so `ϵ ≤ ½` is added (it excludes only undefined cases). The
printed proof uses `ϵ ≤ 1/4`; the statement is claimed on all of `(0, ½]`. -/
theorem lemma_6_1_bayes_block (ϵ : ℝ) (hϵ : 0 < ϵ) (hϵ' : ϵ ≤ 1 / 2) (m : ℕ) :
    (m : ℝ) / 2 - 2 * ϵ ^ 2 * (m : ℝ) ^ ((3 : ℝ) / 2) ≤
      bayesMistakes (blockLabelLaw (m := m) ϵ) := by sorry

end MemoryRegret
