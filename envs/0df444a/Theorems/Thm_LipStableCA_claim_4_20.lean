-- Prove2me | Theorems.Thm_LipStableCA_claim_4_20
-- name    : LipStableCA.claim_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:52.479167+00:00
-- url     : https://prove2.me/theorems/8b3987e1-42e4-48b6-b074-b14a715242d7
-- title:
--   Claim 4.20 — the laws at the two labels are at EMD at least $r/4$
-- statement:
--   Let $\ell,\sigma,\sigma'$ be as in Claim 4.19: the codes differ only in coordinate $\ell$ and $e_\ell(\sigma)+e_\ell(\sigma')\le 3/8$. Then
--   $$\mathrm{EMD}(P^\sigma,P^{\sigma'})\ge\frac r4.$$
--
--   Differences from the source:
--   - encoding: the words $z^b$ of Claim 4.13, fixed once in the construction → an arbitrary map $z$ with the property of Claim 4.13 (`IsCodeMap`); reason: every such $z$ serves the construction; existence is Claim 4.13 itself
--   - encoding: a fixed randomized mechanism, truthful or not → its allocation laws $P$, any map from valid profiles to laws; reason: only the laws enter; this covers every mechanism
--   - encoding: $\ell,\sigma,\sigma'$ fixed by Claim 4.19 → any triple with the two properties of Claim 4.19, as hypotheses; reason: the printed proof uses exactly these properties
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 4.20, p.20

import Definitions.Def_LipStableCA_hardProfile
import Definitions.Def_LipStableCA_IsLipschitz

namespace LipStableCA

/-- **Claim 4.20.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.20. **Formalization Note.** an arbitrary map `z` with the property of Claim 4.13 (`IsCodeMap`): every such `z` serves the construction; existence is Claim 4.13 itself. its allocation laws `P`, any map from valid profiles to laws: only the laws enter; this covers every mechanism. any triple with the two properties of Claim 4.19, as hypotheses: the printed proof uses exactly these properties. -/
theorem claim_4_20 {m : ℕ} (hm : 32 ≤ m) (z : CodeMap m) (hz : IsCodeMap z) {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ ≤ 1 / 16)
    (P : Profile 2 m → Alloc 2 m → ℝ) (hP : ∀ v, IsProfile v → IsLaw (P v))
    (happ : IsApprox P (1 - ϵ)) (l : Fin (codeLength m)) (σ σ' : Code m)
    (hne : σ l ≠ σ' l) (heq : ∀ j, j ≠ l → σ j = σ' j)
    (hsum : decodeError z (P (hardProfile z ϵ σ)) σ l + decodeError z (P (hardProfile z ϵ σ')) σ' l ≤ 3 / 8) :
    (pairCount m : ℝ) / 4 ≤ emd (P (hardProfile z ϵ σ)) (P (hardProfile z ϵ σ')) := by sorry

end LipStableCA
