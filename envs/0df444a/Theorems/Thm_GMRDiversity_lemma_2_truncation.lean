-- Prove2me | Theorems.Thm_GMRDiversity_lemma_2_truncation
-- name    : GMRDiversity.lemma_2_truncation
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:44:22.026201+00:00
-- url     : https://prove2.me/theorems/16080d7b-8e64-4cfc-b0dc-0ef9552df795
-- title:
--   Proof of Lemma 2, truncation — $\mathbb E\tau\le K$ implies $V^\pi_{\lceil3K\rceil}\ge2/3$
-- statement:
--   Let $\pi$ be any live-pool policy on the parity instance (with $x$ uniform) and $K\in\mathbb R$. If $\mathbb E\tau\le K$, where $\tau$ is the number of queries until the target is first queried, then with $T:=\lceil 3K\rceil$, Markov's inequality gives $\mathbb P(\tau>T)\le 1/3$, and therefore
--   $$
--   V^\pi_T\ge\mathbb P(\tau\le T)\ge\tfrac23.
--   $$
--
--   Differences from the source:
--   - generalization: the policy π constructed in the proof and K = C_0(w + 2^{n−w}) → every LivePoolPolicy n w and every real K; reason: the Markov step uses only E τ ≤ K
--   - reading: τ = number of queries until the first correct guess is synthesized → the first round at which the target is queried, through expectedHit; reason: the policy stops whenever the target is queried (p.10, 'Stop whenever the target is queried'), so its τ ends at the first query of the target, by synthesis or earlier; Truncation uses τ only through V^π_T ≥ P(τ ≤ T), which needs exactly this τ
--   - encoding: V^π_T = E[max_{t∈[T]} U_x(z_t)] with x uniform → 2^{-n} Σ_x P(some z_t, t ≤ T, has first coordinate x), with V^π_0 = 0; reason: U_x ∈ {0,1}; the empty maximum is 0
--   - encoding: the general GMR framework of Definition 1 with costs c(Gen_x) = c(XOR) = 1 → only the parity instance: candidates V n × ZMod 2, Gen_x as genLaw, XOR as +, U_x as hit; reason: T counts queries, so costs play no role; the page's statements concern 𝔊^par_x only
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, 'Truncation', p.12

import Mathlib
import Definitions.Def_GMRDiversity_expectedHit

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 2: truncation** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with
Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, proof of Lemma 2,
"Truncation", p.12): if `E τ ≤ K`, then with `T := ⌈3K⌉`, Markov's inequality gives
`P(τ > T) ≤ 1/3`, and therefore `V^π_T(𝔊^par_x) ≥ P(τ ≤ T) ≥ 2/3`.

**Formalization Note.** Stated for every live-pool policy and every bound `K` (the page has
`K = C₀(w + 2^{n−w})` for its policy); `E τ` is `expectedHit` and `⌈·⌉` is `Nat.ceil`. -/
theorem lemma_2_truncation {n w : ℕ} (π : LivePoolPolicy n w) (K : ℝ)
    (hK : expectedHit π ≤ ENNReal.ofReal K) :
    2 / 3 ≤ value π ⌈3 * K⌉₊ := by sorry

end GMRDiversity
