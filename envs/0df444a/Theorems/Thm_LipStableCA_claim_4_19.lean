-- Prove2me | Theorems.Thm_LipStableCA_claim_4_19
-- name    : LipStableCA.claim_4_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:37.886619+00:00
-- url     : https://prove2.me/theorems/08c641f6-3c5b-48d1-9323-118b012fb95c
-- title:
--   Claim 4.19 — a coordinate and two neighbouring labels with small decoding error
-- statement:
--   For the allocation laws $P$ of a $(1-\epsilon)$-approximate rule, there exist a coordinate $\ell\in[k]$ and a pair of codes $\sigma,\sigma'\in\{0,1\}^k$ that differ only in coordinate $\ell$ such that
--   $$e_\ell(\sigma)+e_\ell(\sigma')\le\frac38.$$
--
--   Differences from the source:
--   - encoding: the words $z^b$ of Claim 4.13, fixed once in the construction → an arbitrary map $z$ with the property of Claim 4.13 (`IsCodeMap`); reason: every such $z$ serves the construction; existence is Claim 4.13 itself
--   - encoding: a fixed randomized mechanism, truthful or not → its allocation laws $P$, any map from valid profiles to laws; reason: only the laws enter; this covers every mechanism
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 4.19, p.20

import Definitions.Def_LipStableCA_hardProfile
import Definitions.Def_LipStableCA_IsLipschitz

namespace LipStableCA

/-- **Claim 4.19.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.20. **Formalization Note.** an arbitrary map `z` with the property of Claim 4.13 (`IsCodeMap`): every such `z` serves the construction; existence is Claim 4.13 itself. its allocation laws `P`, any map from valid profiles to laws: only the laws enter; this covers every mechanism. -/
theorem claim_4_19 {m : ℕ} (hm : 32 ≤ m) (z : CodeMap m) (hz : IsCodeMap z) {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ ≤ 1 / 16)
    (P : Profile 2 m → Alloc 2 m → ℝ) (hP : ∀ v, IsProfile v → IsLaw (P v))
    (happ : IsApprox P (1 - ϵ)) :
    ∃ (l : Fin (codeLength m)) (σ σ' : Code m), σ l ≠ σ' l ∧ (∀ j, j ≠ l → σ j = σ' j) ∧
      decodeError z (P (hardProfile z ϵ σ)) σ l + decodeError z (P (hardProfile z ϵ σ')) σ' l ≤ 3 / 8 := by sorry

end LipStableCA
