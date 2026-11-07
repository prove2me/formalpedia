-- Prove2me | Theorems.Thm_LipStableCA_claim_4_13
-- name    : LipStableCA.claim_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:07.631678+00:00
-- url     : https://prove2.me/theorems/259f1990-2873-4ad3-9513-67c14e03d15a
-- title:
--   Claim 4.13 — a code of $2^k$ words with pairwise Hamming distance above $r/4$
-- statement:
--   Let $m\ge 32$, $r=\lfloor m/2\rfloor$, $c_0=1-h_2(1/4)$ and $k=\lfloor c_0r\rfloor$. There are binary words $z^b\in\{0,1\}^r$, indexed by $b\in\{0,1\}^k$, such that
--   $$\mathrm{Ham}(z^b,z^{b'})>\frac r4\qquad\text{for all distinct }b,b'\in\{0,1\}^k.$$
--
--   These words index the good allocations of the lower bound.
--
--   Differences from the source:
--   - encoding: $m\ge 32$, $r=\lfloor m/2\rfloor$, $k=\lfloor c_0r\rfloor$ from the enclosing construction → the hypothesis `32 ≤ m` and the definitions `pairCount`, `codeLength`; reason: the claim is stated in the setting of the family of p.18
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 4.13, p.18

import Definitions.Def_LipStableCA_hardProfile

namespace LipStableCA

/-- **Claim 4.13.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.18. **Formalization Note.** the hypothesis `32 ≤ m` and the definitions `pairCount`, `codeLength`: the claim is stated in the setting of the family of p.18. -/
theorem claim_4_13 {m : ℕ} (hm : 32 ≤ m) : ∃ z : CodeMap m, IsCodeMap z := by sorry

end LipStableCA
