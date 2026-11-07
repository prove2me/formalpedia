-- Prove2me | Theorems.Thm_LipStableCA_claim_4_21
-- name    : LipStableCA.claim_4_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:24.563768+00:00
-- url     : https://prove2.me/theorems/e774190d-af19-4201-9627-f8ab546bde5b
-- title:
--   Claim 4.21 — $K\ge rk/(64\epsilon)$
-- statement:
--   For a $(1-\epsilon)$-approximate and $K$-Lipschitz rule on two bidders, with $m\ge 32$ and $0<\epsilon\le 1/16$,
--   $$K\ge\frac{rk}{64\,\epsilon}.$$
--
--   Differences from the source:
--   - encoding: the words $z^b$ of Claim 4.13, fixed once in the construction → an arbitrary map $z$ with the property of Claim 4.13 (`IsCodeMap`); reason: every such $z$ serves the construction; existence is Claim 4.13 itself
--   - encoding: a fixed randomized mechanism, truthful or not → its allocation laws $P$, any map from valid profiles to laws; reason: only the laws enter; this covers every mechanism
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 4.21, p.20

import Definitions.Def_LipStableCA_hardProfile
import Definitions.Def_LipStableCA_IsLipschitz

namespace LipStableCA

/-- **Claim 4.21.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.20. **Formalization Note.** an arbitrary map `z` with the property of Claim 4.13 (`IsCodeMap`): every such `z` serves the construction; existence is Claim 4.13 itself. its allocation laws `P`, any map from valid profiles to laws: only the laws enter; this covers every mechanism. -/
theorem claim_4_21 {m : ℕ} (hm : 32 ≤ m) (z : CodeMap m) (hz : IsCodeMap z) {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ ≤ 1 / 16)
    (P : Profile 2 m → Alloc 2 m → ℝ) (hP : ∀ v, IsProfile v → IsLaw (P v))
    (happ : IsApprox P (1 - ϵ)) (K : ℝ) (hK : IsLipschitz P K) :
    (pairCount m : ℝ) * (codeLength m : ℝ) / (64 * ϵ) ≤ K := by sorry

end LipStableCA
