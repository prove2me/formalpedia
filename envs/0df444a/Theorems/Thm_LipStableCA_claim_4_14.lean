-- Prove2me | Theorems.Thm_LipStableCA_claim_4_14
-- name    : LipStableCA.claim_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:42.040471+00:00
-- url     : https://prove2.me/theorems/f8c680ab-89dd-4f33-9510-b2449e665793
-- title:
--   Claim 4.14 — good allocations are far apart
-- statement:
--   For all distinct $b,b'\in\{0,1\}^k$, the good allocations $G_b$ and $G_{b'}$ satisfy
--   $$\|X(G_b)-X(G_{b'})\|_1=4\,\mathrm{Ham}(z^b,z^{b'})>r.$$
--
--   Hence any coupling that moves between two different good allocations pays more than $r$.
--
--   Differences from the source:
--   - encoding: the words $z^b$ of Claim 4.13, fixed once in the construction → an arbitrary map $z$ with the property of Claim 4.13 (`IsCodeMap`); reason: every such $z$ serves the construction; existence is Claim 4.13 itself
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 4.14, p.18

import Definitions.Def_LipStableCA_hardProfile

namespace LipStableCA

/-- **Claim 4.14.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.18. **Formalization Note.** an arbitrary map `z` with the property of Claim 4.13 (`IsCodeMap`): every such `z` serves the construction; existence is Claim 4.13 itself. -/
theorem claim_4_14 {m : ℕ} (hm : 32 ≤ m) (z : CodeMap m) (hz : IsCodeMap z) (b b' : Code m)
    (hb : b ≠ b') :
    l1Dist (goodAlloc z b) (goodAlloc z b') = 4 * (hammingDist (z b) (z b') : ℝ) ∧
      (pairCount m : ℝ) < 4 * (hammingDist (z b) (z b') : ℝ) := by sorry

end LipStableCA
