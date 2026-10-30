-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_etaStar_tendsto_one
-- name    : MarketplaceLeakage.Communication.etaStar_tendsto_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:06:13.103523+00:00
-- url     : https://prove2.me/theorems/6f88c48a-92ff-418c-b7dc-89df632980a4
-- title:
--   $\eta^*\to1$ as $q\to1$, and $qv>c$ for $q$ close to one
-- statement:
--   Let $0<c<v$ and let $\eta^*(q)$ be the crossing point of the two ban options,
--
--   $$
--   \eta^*(q)=\frac{qv(2-q)-c-q\sqrt{(1-q)v(v-c)}}{qv(3(1-q)+q^2)-c}.
--   $$
--
--   Then
--
--   $$
--   \lim_{q\to1^-}\eta^*(q)=1,
--   $$
--
--   and $qv>c$ holds for every $q<1$ close enough to $1$.
--
--   In the proof of Proposition 3 these two facts give that the marketplace always prefers to ban communication when $q$ is close enough to one.
--
--   Differences from the source:
--
--   - encoding: lim_{q→1} → the left limit q → 1⁻; reason: q < 1 in the model
--   - reading: "..., this implies M always prefers to ban communication if q is close enough to one" → the item states the sentence's two premises; the consequence is clause (iii) of the goal theorem; reason: the consequence is Proposition 3's third claim and is stated, at full strength, in the goal
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §8.4 (proof of Proposition 3), unnumbered, p. 38

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_etaStar

namespace MarketplaceLeakage.Communication

open Filter Topology

/-- **`η* → 1` as `q → 1`, and `qv > c` for `q` close enough to one.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §8.4 (proof of Proposition 3), unnumbered, p. 38: "Since limq→1 η∗ = 1 and qv > c holds
if q is close enough to one, this implies M always prefers to ban communication if q is close
enough to one."

For `0 < c < v` (pp. 5–6): `η*(q) → 1` as `q → 1⁻`, and `qv > c` for all `q < 1` close
enough to `1`. (The consequence drawn in the sentence, "M always prefers to ban communication
if q is close enough to one", is clause (iii) of the goal `proposition_3_ban_communication`.)

**Formalization Note.** `q < 1` in the model, so `lim_{q→1}` is the left limit
(`𝓝[<] 1`). -/
theorem etaStar_tendsto_one {v c : ℝ} (hc : 0 < c) (hcv : c < v) :
    Tendsto (fun q => etaStar q v c) (𝓝[<] 1) (𝓝 1) ∧
      ∀ᶠ q in 𝓝[<] (1 : ℝ), c < q * v := by sorry

end MarketplaceLeakage.Communication
