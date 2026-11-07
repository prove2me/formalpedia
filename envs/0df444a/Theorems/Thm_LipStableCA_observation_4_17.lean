-- Prove2me | Theorems.Thm_LipStableCA_observation_4_17
-- name    : LipStableCA.observation_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:31.8578+00:00
-- url     : https://prove2.me/theorems/d9abb7f9-9bd5-4396-af1f-e3202be36030
-- title:
--   Observation 4.17 — welfare of good and bad allocations in the hard family
-- statement:
--   Fix $\sigma\in\{0,1\}^k$. Then:
--
--   1. $W_{v^\sigma}(G_b)=2+\beta^\sigma_b$ for every $b\in\{0,1\}^k$;
--   2. $W_{v^\sigma}(S)\le 1+16\epsilon$ for every allocation $S$ that is not good;
--   3. $\mathrm{OPT}(v^\sigma)=2+16\epsilon$;
--   4. every allocation $S$ satisfies $\mathrm{OPT}(v^\sigma)-W_{v^\sigma}(S)\ge\frac{16\epsilon}{k}\mathrm{Ham}(\mathrm{dec}(S),\sigma)$;
--   5. $\mathrm{OPT}(v^\sigma)-W_{v^\sigma}(S)\ge 1$ for every allocation $S$ that is not good.
--
--   A near-optimal rule must therefore decode most bits of the label.
--
--   Differences from the source:
--   - encoding: the words $z^b$ of Claim 4.13, fixed once in the construction → an arbitrary map $z$ with the property of Claim 4.13 (`IsCodeMap`); reason: every such $z$ serves the construction; existence is Claim 4.13 itself
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Observation 4.17, p.19

import Definitions.Def_LipStableCA_hardProfile
open ComplementFreeCA.CFRounding

namespace LipStableCA

/-- **Observation 4.17.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.19. **Formalization Note.** an arbitrary map `z` with the property of Claim 4.13 (`IsCodeMap`): every such `z` serves the construction; existence is Claim 4.13 itself. -/
theorem observation_4_17 {m : ℕ} (hm : 32 ≤ m) (z : CodeMap m) (hz : IsCodeMap z) {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ ≤ 1 / 16) (σ : Code m) :
    (∀ b, welfare (hardProfile z ϵ σ) (goodAlloc z b).1 = 2 + bonus ϵ σ b) ∧
    (∀ S : Alloc 2 m, ¬ IsGood z S → welfare (hardProfile z ϵ σ) S.1 ≤ 1 + 16 * ϵ) ∧
    opt (hardProfile z ϵ σ) = 2 + 16 * ϵ ∧
    (∀ S : Alloc 2 m, 16 * ϵ / (codeLength m : ℝ) * (hammingDist (decode z S) σ : ℝ) ≤
      opt (hardProfile z ϵ σ) - welfare (hardProfile z ϵ σ) S.1) ∧
    (∀ S : Alloc 2 m, ¬ IsGood z S → 1 ≤ opt (hardProfile z ϵ σ) - welfare (hardProfile z ϵ σ) S.1) := by sorry

end LipStableCA
