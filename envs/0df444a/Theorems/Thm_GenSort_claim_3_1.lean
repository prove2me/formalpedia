-- Prove2me | Theorems.Thm_GenSort_claim_3_1
-- name    : GenSort.claim_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:28:33.865665+00:00
-- url     : https://prove2.me/theorems/22de43eb-8ca0-4c56-b07c-58bbadb09ad2
-- title:
--   Claim 3.1 — every consistent $\sigma$ has $\mathrm{dist}_F(\pi,\sigma) \le f/(2^{28}\log^2 n)$ with probability $1 - 2^{-10n}$
-- statement:
--   **Standing assumptions of §3.** $F \subseteq E(G)$ and $f = |F| > 2^{24} n \log^2 n$ (otherwise the routine queries all of $F$ and stops).
--
--   Sample $k_0 = 2^{32} n \log^3 n$ edges independently and uniformly at random from $F$, with replacement, and query their orientations. Then, with probability at least $1 - 2^{-10n}$ over the sample, every permutation $\sigma$ of the vertices that agrees with the reported orientation of every sampled edge satisfies
--   $$
--   \mathrm{dist}_F(\pi, \sigma) \le \frac{f}{2^{28} \log^2 n}.
--   $$
--
--   The coarse predictor $\sigma$ is any such permutation, so the claim says that the coarse prediction already errs on at most a $2^{-28}\log^{-2} n$ fraction of $F$.
--
--   Differences from the source:
--   - reading: σ is any permutation agreeing with every sampled edge → the event holds simultaneously for every such σ; reason: the page's choice is arbitrary, and the universal reading is the stronger one
--   - reading: sample size 2³²n log³ n (a real number) → ⌈2³² n log₂³ n⌉; reason: a sample size is an integer; rounding up only enlarges the sample
--   - reading: log n with no base fixed → log₂ n; reason: the paper never fixes the base; every constant on the path was checked for base 2
--   - encoding: with probability 1 − 2^{−10n} → probability at least 1 − 2^{−10n}, as the fraction of sample sequences in F^{k₀}; reason: i.i.d. uniform sampling with replacement is the uniform distribution on F^{k₀}
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.1, p.5 (PDF p.7), with the sampling set-up of §3.1, p.5

import Mathlib
import Definitions.Def_GenSort_k0
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_GenSort_AgreesOn
import Definitions.Def_GenSort_distOrd
import Definitions.Def_GenSort_CoarseGood

namespace GenSort

/-- **Claim 3.1** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.1, p.5, PDF p.7). Let `F ⊆ E(G)` with `f = |F| > 2^24 n log² n`. Sample
`2^32 n log³ n` edges uniformly at random from `F` (with replacement). With probability at least
`1 − 2^{−10n}` over the sample, every permutation `σ` that agrees with the reported orientation
of every sampled edge satisfies `dist_F(π, σ) ≤ f / (2^28 log² n)` (the event `CoarseGood`).

**Formalization Note.** "Any permutation which agrees" (the page's arbitrary choice) is read
universally: the event holds simultaneously for every consistent `σ`. The sample is a uniform
element of `Fin k0 → F`, `k0 = ⌈2^32 n log₂³ n⌉`; `log` is `log₂`. The standing assumptions of §3
(`F ⊆ E`, `f > 2^24 n log² n`) are hypotheses. -/
theorem claim_3_1 {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n)))
    (hFG : (↑F : Set (Sym2 (Fin n))) ⊆ G.edgeSet)
    (hf : (2 : ℝ) ^ 24 * n * Real.logb 2 n ^ 2 < F.card) (π : Equiv.Perm (Fin n)) :
    1 - 1 / (2 : ℝ) ^ (10 * n) ≤ PunctSketch.coinProb (Ω := Fin (k0 n) → F) fun x =>
      ∀ σ : Equiv.Perm (Fin n), (∀ i, AgreesOn π σ (x i : Sym2 (Fin n))) → CoarseGood F π σ := by sorry

end GenSort
