-- Prove2me | Theorems.Thm_LipStableCA_lemma_2_8_part_1
-- name    : LipStableCA.lemma_2_8_part_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:48:01.512205+00:00
-- url     : https://prove2.me/theorems/fee34137-74f6-44bd-b3c4-b934cca1d746
-- title:
--   Lemma 2.8, part 1 — 1-Lipschitz test functions and marginals are bounded by EMD
-- statement:
--   Let $\mu,\nu$ be distributions on the set $\mathcal A$ of allocations. If $f:\mathcal A\to\mathbb R$ satisfies $|f(S)-f(T)|\le\|X(S)-X(T)\|_1$ for all allocations $S,T$, then
--   $$\bigl|\mathbb E_{S\sim\mu}[f(S)]-\mathbb E_{T\sim\nu}[f(T)]\bigr|\le \mathrm{EMD}(\mu,\nu).$$
--   In particular, the allocation marginals $A_\mu=\mathbb E_{S\sim\mu}[X(S)]$ and $A_\nu=\mathbb E_{T\sim\nu}[X(T)]$ satisfy $\|A_\mu-A_\nu\|_1\le\mathrm{EMD}(\mu,\nu)$.
--
--   This is the easy direction of duality for the earth mover distance. Lemma 5.4 uses it on the marginal of one bidder. Parts 4 and 5 of Lemma 2.8 are not used on the path to the main results and are not part of this mission.
--
--   Differences from the source:
--   - encoding: distributions on $\mathcal A$ → real mass functions (`IsLaw`); reason: $\mathcal A$ is finite; same objects
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 2.8, part 1, p.8

import Definitions.Def_LipStableCA_emd

namespace LipStableCA

/-- **Lemma 2.8, part 1.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.8. **Formalization Note.** real mass functions (`IsLaw`): `A` is finite; same objects. -/
theorem lemma_2_8_part_1 {n m : ℕ} (μ ν : Alloc n m → ℝ) (hμ : IsLaw μ) (hν : IsLaw ν) :
    (∀ f : Alloc n m → ℝ, (∀ S T, |f S - f T| ≤ l1Dist S T) →
      |∑ S, μ S * f S - ∑ T, ν T * f T| ≤ emd μ ν) ∧
    ∑ i, ∑ j, |marginal μ i j - marginal ν i j| ≤ emd μ ν := by sorry

end LipStableCA
