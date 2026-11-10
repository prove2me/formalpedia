-- Prove2me | Theorems.Thm_LEDPCount_lemma_2_16
-- name    : LEDPCount.lemma_2_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:13.241191+00:00
-- url     : https://prove2.me/theorems/0c993846-b4fc-46cf-b6c9-39569d09f2b7
-- title:
--   Lemma 2.16 — randomized response is an $\varepsilon$-local randomizer
-- statement:
--   For every $t$ and every $\varepsilon>0$, randomized response $\mathrm{RR}_\varepsilon$ on $t$-bit vectors is an $\varepsilon$-local randomizer: for all $a,a'\in\{0,1\}^t$ differing in exactly one coordinate and every set $S$ of $t$-bit vectors,
--   $$
--   \Pr[\mathrm{RR}_\varepsilon(a)\in S]\le e^{\varepsilon}\,\Pr[\mathrm{RR}_\varepsilon(a')\in S].
--   $$
--   This is the privacy of the first round of LNC.
--
--   Differences from the source:
--   - encoding: bits in {0,1} → Bool; reason: Lean convention; same instances
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Lemma 2.16, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_LEDPCount_IsLocalRandomizer
import Definitions.Def_LEDPCount_rr

namespace LEDPCount

open MeasureTheory

/-- Lemma 2.16 (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.17, PDF p.19): Randomized Response `RR_ε` on `t`-bit vectors
(Definition 2.15, `ε > 0`) is an ε-local randomizer (Definition 2.14). -/
theorem lemma_2_16 (t : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IsLocalRandomizer (fun a : Fin t → Bool => rr ε a) ε := by sorry

end LEDPCount
