-- Prove2me | Theorems.Thm_LosslessCond_lemma_5_1
-- name    : LosslessCond.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:24.076432+00:00
-- url     : https://prove2.me/theorems/026e5495-9e75-4592-967f-e58dfc97ed83
-- title:
--   Lemma 5.1 — a finite hitting set of size $a(r,s)=B(r)2^s$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix with $\operatorname{rank}(M)\le r$, $r\ge 1$, and let $s\ge 0$. Let $\mu$ be any probability distribution on the columns $Y$. Then there is a nonempty set $S\subseteq Y$ of original column labels with
--   $$
--   |S|\le a(r,s)=B(r)2^s
--   $$
--   that meets every complement $Y\setminus G$ with $G\in C_s$ and $\mu(Y\setminus G)\ge 1/2$.
--
--   Meeting $Y\setminus G$ means containing a column on which the corresponding partial protocol cannot be completed. Lemma 5.2 applies this with uniform distributions on the columns not yet covered.
--
--   Differences from the source:
--   - encoding: any distribution on the columns → μ : Y → ℝ with μ ≥ 0 and ∑ μ = 1; reason: distributions on a finite set are exactly such weight functions; full support is not required
--   - generalization: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite nonempty set is equivalent to a type in universe 0, so every instance of the source is covered; the instances with an empty X or Y are additional, and there the statement holds trivially
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Lemma 5.1, (5.1), p.13 (PDF p.14)

import Mathlib
import Definitions.Def_DetCCHard_realRank
import Definitions.Def_LosslessCond_domainFamily
import Definitions.Def_LosslessCond_B

namespace LosslessCond

/-- **Lemma 5.1 (A finite hitting set)** (Mackenzie, *Lossless Hardness Condensation in
Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.13,
(5.1)). Let `rank(M) ≤ r` with `r ≥ 1`, and let `s ≥ 0`. Under any distribution `μ` on the columns,
there is a set `S` of size at most `a(r, s) = B(r)·2^s` meeting every complement `Y \ G` with
`G ∈ C_s` and probability mass at least `1/2`. The set can be chosen nonempty and uses original
column labels.

**Formalization Note** A distribution on the finite column set is a weight function `μ ≥ 0` with
`∑ μ = 1` (full support is not required). The mass of `Y \ G` is `∑_y 1_{Y∖G}(y) μ(y)`. The set
`S` is a `Finset` of original column labels. -/
theorem lemma_5_1 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (r : ℕ) (hr : 1 ≤ r)
    (hrank : DetCCHard.realRank M ≤ r) (s : ℕ) (μ : Y → ℝ) (hμ0 : ∀ y, 0 ≤ μ y)
    (hμ1 : ∑ y, μ y = 1) :
    ∃ S : Finset Y, S.Nonempty ∧ S.card ≤ a r s ∧
      ∀ G ∈ domainFamily M s, 1 / 2 ≤ ∑ y, (Gᶜ).indicator μ y → ∃ y ∈ S, y ∉ G := by sorry

end LosslessCond
