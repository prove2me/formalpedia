-- Prove2me | Theorems.Thm_LEDPCount_thm_1_1_privacy
-- name    : LEDPCount.thm_1_1_privacy
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:56.153196+00:00
-- url     : https://prove2.me/theorems/8d68b5fd-8661-4f18-91b3-b3e51988be9a
-- title:
--   Proof of Theorem 1.1 — LNC uses $\varepsilon/2$-local randomizers and is $\varepsilon$-LEDP
-- statement:
--   Let $H$ have $k$ vertices and $\ell\ge1$ edges, $n\ge k$ and $\varepsilon\in(0,1]$. In LNC (Algorithm 1):
--   1. each party's round-1 randomizer, and each party's round-2 randomizer for every round-1 transcript, is an $\varepsilon/2$-local randomizer;
--   2. LNC is $\varepsilon$-LEDP: for edge-neighboring graphs $G\sim G'$ and every measurable set $S$ of transcripts, $\Pr[\Pi(G)\in S]\le e^{\varepsilon}\Pr[\Pi(G')\in S]$.
--
--   This is the privacy half of Theorem 1.1: the first round costs $\varepsilon/2$, the second round, conditioned on the first, costs $\varepsilon/2$.
--
--   Differences from the source:
--   - encoding: Algorithm 1 for a pattern on k vertices and an n-vertex graph → n ≥ k assumed; reason: line 11's (n − k)! is undefined for n < k; Theorem 1.1's setting
--   - reading: an ε-LEDP algorithm → every randomizer is a local randomizer, and the transcript law is ε-DP for edge neighbours; reason: Definitions 2.12–2.14: a local algorithm acts only through local randomizers
--   - encoding: the interactive local model → the two-round fixed-schedule protocol type TwoRoundLocal; reason: LNC has exactly this shape
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), proof of Theorem 1.1, privacy, p.18–19 (PDF p.20–21)

import Mathlib
import Definitions.Def_LEDPCount_IsLocalRandomizer
import Definitions.Def_LEDPCount_lnc

namespace LEDPCount

/-- Proof of Theorem 1.1, privacy of LNC (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.18–19, PDF p.20–21): for a pattern
`H` with `k` vertices and `ℓ ≥ 1` edges, `n ≥ k` and `ε ∈ (0, 1]`, every randomizer of
Algorithm 1 (each party's round-1 randomized response, and each party's round-2 Laplace release
for every round-1 transcript) is an `ε/2`-local randomizer, and LNC is ε-LEDP. -/
theorem thm_1_1_privacy {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) (n : ℕ) (hkn : k ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ i : Fin n, IsLocalRandomizer ((lnc H n ε).round1 i) (ε / 2) ∧
      ∀ y : Fin n → Fin n → Bool, IsLocalRandomizer ((lnc H n ε).round2 i y) (ε / 2)) ∧
    (lnc H n ε).IsLEDP ε := by sorry

end LEDPCount
