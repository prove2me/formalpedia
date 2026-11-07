-- Prove2me | Theorems.Thm_LipStableCA_claim_4_18
-- name    : LipStableCA.claim_4_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:01.840568+00:00
-- url     : https://prove2.me/theorems/4d87f50a-2b12-4b06-8116-129163a5fb2d
-- title:
--   Claim 4.18 — an approximate rule is good and decodes most bits
-- statement:
--   Let $P$ be the allocation laws of a $(1-\epsilon)$-approximate rule on two bidders. For every $\sigma\in\{0,1\}^k$,
--   $$\Pr_{S\sim P^\sigma}[S\text{ is not good}]\le 3\epsilon\qquad\text{and}\qquad\sum_{\ell=1}^k e_\ell(\sigma)\le\frac{3k}{16},$$
--   where $P^\sigma$ is the law at $v^\sigma$ and $e_\ell(\sigma)=\Pr_{S\sim P^\sigma}[\mathrm{dec}(S)_\ell\ne\sigma_\ell]$.
--
--   Differences from the source:
--   - encoding: the words $z^b$ of Claim 4.13, fixed once in the construction → an arbitrary map $z$ with the property of Claim 4.13 (`IsCodeMap`); reason: every such $z$ serves the construction; existence is Claim 4.13 itself
--   - encoding: a fixed randomized mechanism, truthful or not → its allocation laws $P$, any map from valid profiles to laws; reason: only the laws enter; this covers every mechanism
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 4.18, p.19

import Definitions.Def_LipStableCA_hardProfile
import Definitions.Def_LipStableCA_IsLipschitz
open Classical

namespace LipStableCA

/-- **Claim 4.18.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.19. **Formalization Note.** an arbitrary map `z` with the property of Claim 4.13 (`IsCodeMap`): every such `z` serves the construction; existence is Claim 4.13 itself. its allocation laws `P`, any map from valid profiles to laws: only the laws enter; this covers every mechanism. -/
theorem claim_4_18 {m : ℕ} (hm : 32 ≤ m) (z : CodeMap m) (hz : IsCodeMap z) {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ ≤ 1 / 16)
    (P : Profile 2 m → Alloc 2 m → ℝ) (hP : ∀ v, IsProfile v → IsLaw (P v))
    (happ : IsApprox P (1 - ϵ)) (σ : Code m) :
    ∑ S, (if IsGood z S then 0 else P (hardProfile z ϵ σ) S) ≤ 3 * ϵ ∧
      ∑ l, decodeError z (P (hardProfile z ϵ σ)) σ l ≤ 3 * (codeLength m : ℝ) / 16 := by sorry

end LipStableCA
