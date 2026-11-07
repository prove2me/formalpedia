-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_3_3
-- name    : OnlineBinCover.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:51.240012+00:00
-- url     : https://prove2.me/theorems/a19d2d8f-f083-45bb-b6f8-588b01febb83
-- title:
--   Lemma 3.3 — a uniform sample covers $(1-4\varepsilon)p\,\mathrm{OPT}(I)-O(pK\mathrm{vol}(I)^{5/6}+K)$ bins
-- statement:
--   There are absolute constants $C,c>0$ such that the following holds. Let $0<\varepsilon<1/8$, $K=\lceil\varepsilon^{-2}\rceil$, $0<p\le1$, and let $I$ be an instance of $n$ items with sizes in $(0,1]$ and $\mathrm{vol}(I)\ge1$. Let $I_p$ be a uniformly random subset of $I$ of size $\lfloor pn\rfloor$. Then
--
--   $$\mathrm{OPT}(I_p)\ge(1-4\varepsilon)\,p\,\mathrm{OPT}(I)-C\big(pK\,\mathrm{vol}(I)^{5/6}+K\big)$$
--
--   with probability at least $1-CK\exp(-c\,p\,\mathrm{vol}(I)^{1/6})$.
--
--   The lemma says that a random sample is a scaled-down copy of the instance; it gives the size of the blueprint and, in Algorithm 4, the optimum of each epoch.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$, $\Omega(\cdot)$ → absolute constants $C,c>0$ chosen before $\varepsilon$, $p$ and the instance; reason: the paper writes the dependence on $K,\varepsilon,p$ explicitly
--   - encoding: a uniformly random subset of $\lfloor pn\rfloor$ items → the first $\lfloor pn\rfloor$ arrivals of a uniform permutation, probability the fraction of the $n!$ permutations; reason: the same law
--   - reading: the sampling fraction $p$ (Algorithm 2's input; $I_p$ has $\lfloor pn\rfloor$ items of $I$) → $0<p\le1$; reason: a sampling fraction of the input; this is the range the paper uses (App. B.6 takes $p<1$)
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma 3.3, p.9 (PDF p.10); proof App. B.6, pp.27–30

import Mathlib
import Definitions.Def_OnlineBinCover_Blueprint

namespace OnlineBinCover

/-- Lemma 3.3 (Sample covering), p.9. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

There are absolute constants `C, c > 0` such that for every `ε ∈ (0, 1/8)` with `K = ⌈ε^{-2}⌉`,
every `p ∈ (0, 1]` and every instance with sizes in `(0, 1]` and `vol(I) ≥ 1`, the uniformly random
sample `Ip` of `⌊pn⌋` items (the first `⌊pn⌋` arrivals of a uniform order) satisfies
`OPT(Ip) ≥ (1 − 4ε) p OPT(I) − C (p K vol(I)^{5/6} + K)` with probability at least
`1 − C K exp(−c p vol(I)^{1/6})`. -/
theorem lemma_3_3 : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 8 → ∀ p : ℝ, 0 < p → p ≤ 1 →
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → 1 ≤ vol s →
      1 - C * (Kof ε : ℝ) * Real.exp (-(c * p * vol s ^ ((1 : ℝ) / 6))) ≤
        DynamicOnlineLP.DLA.probPerm (fun σ : Equiv.Perm (Fin n) =>
          (1 - 4 * ε) * p * (OPT s : ℝ) -
              C * (p * (Kof ε : ℝ) * vol s ^ ((5 : ℝ) / 6) + (Kof ε : ℝ)) ≤
            (OPTon s (smp σ ⌊p * n⌋₊) : ℝ)) := by sorry

end OnlineBinCover
