-- Prove2me | Theorems.Thm_LipStableCA_lemma_2_8_part_3
-- name    : LipStableCA.lemma_2_8_part_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:57.1672+00:00
-- url     : https://prove2.me/theorems/1805181e-039e-4db5-a123-a656b0cff4a6
-- title:
--   Lemma 2.8, part 3 — unilateral bounds imply the Lipschitz bound
-- statement:
--   Let $S$ be an allocation rule with allocation laws $P_v$, and let $K\ge 0$. Suppose that $\mathrm{EMD}(P_v,P_w)\le K\,\delta_i(v,w)$ for every bidder $i$ and all profiles $v,w$ with $v_{-i}=w_{-i}$ and $\delta_i(v,w)<\infty$. Then $S$ is $K$-Lipschitz, that is, $\mathrm{EMD}(P_v,P_w)\le K\,d(v,w)$ whenever $d(v,w)<\infty$.
--
--   All the upper bounds of the paper are proved for a change in the report of one bidder and pass through this lemma.
--
--   Differences from the source:
--   - encoding: distributions on $\mathcal A$ → real mass functions (`IsLaw`); reason: $\mathcal A$ is finite; same objects
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 2.8, part 3, p.8

import Definitions.Def_LipStableCA_IsLipschitz

namespace LipStableCA

/-- **Lemma 2.8, part 3.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.8. **Formalization Note.** real mass functions (`IsLaw`): `A` is finite; same objects. -/
theorem lemma_2_8_part_3 {n m : ℕ} (P : Profile n m → Alloc n m → ℝ)
    (hP : ∀ v, IsProfile v → IsLaw (P v)) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (i : Fin n) (v w : Profile n m), IsProfile v → IsProfile w → (∀ h, h ≠ i → v h = w h) →
      deltaI v w i ≠ ⊤ → emd (P v) (P w) ≤ K * (deltaI v w i).toReal) :
    IsLipschitz P K := by sorry

end LipStableCA
