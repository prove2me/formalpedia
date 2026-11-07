-- Prove2me | Theorems.Thm_LipStableCA_claim_4_16
-- name    : LipStableCA.claim_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:24.57199+00:00
-- url     : https://prove2.me/theorems/adeb3270-f1f1-44f9-81e6-65a49154912b
-- title:
--   Claim 4.16 — codes differing in one bit give profiles at distance at most $16\epsilon/k$
-- statement:
--   If $\sigma,\sigma'\in\{0,1\}^k$ differ only in one coordinate, then
--   $$d(v^\sigma,v^{\sigma'})\le\frac{16\epsilon}{k}.$$
--
--   So one flip of a label costs little in the input distance, and the output must move by $\Omega(r)$ for some flip.
--
--   Differences from the source:
--   - encoding: the words $z^b$ of Claim 4.13, fixed once in the construction → an arbitrary map $z$ with the property of Claim 4.13 (`IsCodeMap`); reason: every such $z$ serves the construction; existence is Claim 4.13 itself
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 4.16, p.19

import Definitions.Def_LipStableCA_hardProfile
import Definitions.Def_LipStableCA_profileDist

namespace LipStableCA

/-- **Claim 4.16.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.19. **Formalization Note.** an arbitrary map `z` with the property of Claim 4.13 (`IsCodeMap`): every such `z` serves the construction; existence is Claim 4.13 itself. -/
theorem claim_4_16 {m : ℕ} (hm : 32 ≤ m) (z : CodeMap m) (hz : IsCodeMap z) {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ ≤ 1 / 16) (σ σ' : Code m) (l : Fin (codeLength m))
    (hne : σ l ≠ σ' l) (heq : ∀ j, j ≠ l → σ j = σ' j) :
    profileDist (hardProfile z ϵ σ) (hardProfile z ϵ σ') ≤
      ENNReal.ofReal (16 * ϵ / (codeLength m : ℝ)) := by sorry

end LipStableCA
