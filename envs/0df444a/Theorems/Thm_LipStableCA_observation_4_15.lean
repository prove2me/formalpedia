-- Prove2me | Theorems.Thm_LipStableCA_observation_4_15
-- name    : LipStableCA.observation_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:39.460138+00:00
-- url     : https://prove2.me/theorems/039940a0-08bd-4e17-80c0-1e4805f85d1d
-- title:
--   Observation 4.15 — the hard valuations are normalized and monotone
-- statement:
--   For every $\sigma\in\{0,1\}^k$, the valuations $v^\sigma_1$ and $v_2$ of the lower-bound family are normalized and monotone. Here $v^\sigma_1(Q)$ is $0$ for $|Q|<r$, is $1+\beta^\sigma_b$ for $Q=B_b$, is $1$ for the other bundles of size $r$, and is $1+16\epsilon$ for $|Q|>r$, while $v_2(Q)=\mathbf 1\{M\setminus B_b\subseteq Q\text{ for some }b\}$.
--
--   So the family lies in the domain of the rule.
--
--   Differences from the source:
--   - encoding: the words $z^b$ of Claim 4.13, fixed once in the construction → an arbitrary map $z$ with the property of Claim 4.13 (`IsCodeMap`); reason: every such $z$ serves the construction; existence is Claim 4.13 itself
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Observation 4.15, p.19

import Definitions.Def_LipStableCA_hardProfile

namespace LipStableCA

/-- **Observation 4.15.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.19. **Formalization Note.** an arbitrary map `z` with the property of Claim 4.13 (`IsCodeMap`): every such `z` serves the construction; existence is Claim 4.13 itself. -/
theorem observation_4_15 {m : ℕ} (hm : 32 ≤ m) (z : CodeMap m) (hz : IsCodeMap z) {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ ≤ 1 / 16) (σ : Code m) :
    IsProfile (hardProfile z ϵ σ) := by sorry

end LipStableCA
