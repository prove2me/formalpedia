-- Prove2me | Theorems.Thm_IIDMultiItem_TwoPoint_lemma_3_1
-- name    : IIDMultiItem.TwoPoint.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:57:39.368459+00:00
-- url     : https://prove2.me/theorems/b6c50bd9-c2a4-4dc8-9a4d-0dd81ba14523
-- title:
--   Lemma 3.1 — ϕ_{c,r} is strictly increasing in r, and ϕ_{d−k,k} in k ∈ {0, …, d − 1}
-- statement:
--   Let $0<a<b$, $0<p<1$, $q=1-p$, $\Delta=b-a$, and for $c\ge1$, $r\ge0$ let $\phi_{c,r}=a-\Delta\Pr[R>r]/(c\Pr[R=r])$ with $R\sim\mathrm{Bin}(c+r,q)$ (3.1). Then:
--   1. for fixed $c\ge1$, $r\mapsto\phi_{c,r}$ is strictly increasing on $\{0,1,2,\dots\}$;
--   2. for fixed $d\ge2$, $k\mapsto\phi_{d-k,k}$ is strictly increasing on $\{0,\dots,d-1\}$.
--
--   The second part makes the set of $k$ with $\phi_{d-k,k}>0$ an upper interval, which is what makes $\theta_d$ in (3.2) a reserve: $k\ge\theta_d\iff\phi_{d-k,k}>0$ for $0\le k<d$ (3.3).
--
--   Differences from the source:
--   - encoding: k ∈ {0, …, d − 1} → StrictMonoOn on Set.Iio d, with d − k in ℕ; reason: the same index set; d − k ≥ 1 there, so no truncated subtraction occurs
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 13 (PDF 15), Lemma 3.1

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Counts

namespace IIDMultiItem.TwoPoint

/-- Lemma 3.1. For fixed `c ≥ 1`, `ϕ_{c,r}` is strictly increasing in `r`. For fixed `d ≥ 2`,
`ϕ_{d−k,k}` is strictly increasing in `k ∈ {0, …, d − 1}`. -/
theorem lemma_3_1 (a b p : ℝ) (ha : 0 < a) (hab : a < b) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ c : ℕ, 1 ≤ c → StrictMono (fun r : ℕ => phi a b p c r)) ∧
    (∀ d : ℕ, 2 ≤ d → StrictMonoOn (fun k : ℕ => phi a b p (d - k) k) (Set.Iio d)) := by sorry

end IIDMultiItem.TwoPoint
