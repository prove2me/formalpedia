-- Prove2me | Theorems.Thm_LocalSweepFT_claim_4_7
-- name    : LocalSweepFT.claim_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:51.50727+00:00
-- url     : https://prove2.me/theorems/3bf32de6-6b8d-4d91-a0b9-0d72582364d5
-- title:
--   Claim 4.7 — the sweep rule always has a suggestion when the local syndrome is a rooted boundary
-- statement:
--   Let $2\le d'<d$, $n\ge1$, $v$ a vertex of $\mathcal T^d_n$ and $\sigma\ne0$ a $(d'-1)$-chain. If some $d'$-chain $z$ rooted at $v$ satisfies $(\partial^-z)|_{v+}=\sigma|_{v+}$, then some $d'$-chain $\tilde z$ rooted at $v$ satisfies the sweep-rule conditions of Def. 4.6:
--   $$\mathrm{Str}^0_+(v,\tilde z)\subseteq\mathrm{Str}^0_+(v,\sigma|_v),\qquad(\partial^-\tilde z)|_{v+}=\sigma|_{v+}.$$
--
--   This answers the conjecture of Kubica and Preskill for face dimension at least two and makes the sweep rule well defined as a decoder.
--
--   Differences from the source:
--   - generalization: standing assumption d′, d − d′ ≥ 2 (p.4) → 2 ≤ d′ < d; reason: the claim prints its own hypothesis d′ ≥ 2 and its base case allows every d ≥ 3; the standing range is a special case
--   - reading: "whose boundary agrees with σ|_{v+}" → (∂⁻z)|_{v+} = σ|_{v+}; reason: agreement on the checks rooted at v, as in the informal statement on p.5
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 4.7, p.19

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_IsSweepRule

namespace LocalSweepFT

/-- Claim 4.7, p.19 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). For `d′ ≥ 2`, let `σ` be a nonzero `(d′−1)`-chain on the
torus `T^d_n` and `v` a vertex. If some `d′`-chain `z` rooted at `v` has `(∂⁻z)|_{v+} = σ|_{v+}`, then
some `d′`-chain `z̃` rooted at `v` satisfies the sweep-rule conditions of Def 4.6.

**Formalization Note.** "Whose boundary agrees with `σ|_{v+}`" is read on the checks rooted at `v`,
`(∂⁻z)|_{v+} = σ|_{v+}`, as in the informal statement on p.5. The sweep-rule conditions are those of
`IsAdmissible` (condition 1 with `σ|_v`, as printed in Def 4.6). -/
theorem claim_4_7 (d d' n : ℕ) [NeZero n] (h1 : 2 ≤ d') (h2 : d' < d) (v : Vtx (ZMod n) d)
    (σ : Chain (ZMod n) d (d' - 1)) (hσ : σ ≠ 0) (z : Chain (ZMod n) d d') (hz : IsRootedAt v z)
    (hzσ : restrictPos v (bdry z) = restrictPos v σ) :
    ∃ zt : Chain (ZMod n) d d', IsAdmissible v σ zt := by sorry

end LocalSweepFT
