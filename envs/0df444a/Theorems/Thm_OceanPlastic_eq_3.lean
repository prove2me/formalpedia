-- Prove2me | Theorems.Thm_OceanPlastic_eq_3
-- name    : OceanPlastic.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:16.999191+00:00
-- url     : https://prove2.me/theorems/f22a4667-4f19-4390-aa43-a6efc0708a21
-- title:
--   Eq. (2)–(3) — the lower stages of Case O (corrected: $r_c\le p_m+r_p$)
-- statement:
--   Let $r_c,r_p\ge0$ with $r_c\le p_m+r_p$, and $r=r_c+r_p$. For every acquisition price $h$, a collector's unique optimal volume is $(h+r_c)/k$, so that the total volume is $q_t(h+r_c)$. The unique solution of the processor's problem $\max_{h\ge0}\,(p_m-h+r_p)\,q_t(h+r_c)$ is
--   $$h(r_c,r_p)=\frac{p_m+r_p-r_c}{2}.$$
--   At this price the volume, the collectors' income $(h+r_c)q_t(h+r_c)$ and the processor's profit are
--   $$V^O(r)=\frac{M(p_m+r)}{2k},\qquad \Pi^O_C(r)=\Pi^O_P(r)=\frac{M(p_m+r)^2}{4k}.$$
--
--   This records the domain on which the closed forms (3), used in the firm's problem (4), are the equilibrium of the lower stages.
--
--   Differences from the source:
--   - correction: h(r_c,r_p) = (p_m+r_p−r_c)/2 and (3) for all bonuses → for r_c ≤ p_m + r_p; reason: for r_c > p_m + r_p the printed h is negative: M = k = 1, p_m = 1, r_p = 0, r_c = 3 gives objective (1−h)(h+3), decreasing on h ≥ 0, so h = 0 and volume 3, not V^O(3) = 2
--   - reading: bonuses r_c, r_p → r_c, r_p ≥ 0; reason: a bonus is a payment to the local supply chain; (4) requires r ≥ 0
--   - reading: "the same derivation as in the Benchmark Case" → the collector's unique maximizer at unit payment h + r_c; reason: this is that derivation, over q ∈ ℝ
--   - reading: M, v̄_o, Q_o unspecified positive sizes; p_m a price; c_E^r with no stated sign → real M, v̄_o, Q_o > 0, p_m ≥ 0, c_E^r ≥ 0 (fields of Params), with k > 0, δ_o ∈ [0,1), ρ_p ∈ (0,1] as printed; reason: sizes, a price and a value; v̄_o is the upper end of a uniform law; M is real as in the paper, which differentiates in M
--   - reading: collectors' total income → gross payment (price received) × (volume); reason: the only reading consistent with Π^B_C = Mp_m²/(4k), eq. (3) and Π^{OS}_C = kq_t²/M (p. 14); net utility would be half of it
-- source:
--   Baron–Romero–Zhang–Zhou, Innovative Business Models in Ocean-Bound Plastic Recycling, MSOM, doi:10.1287/msom.2022.0643, §3.2(a), eq. (2)–(3), p.10

import Mathlib
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark
import Definitions.Def_OceanPlastic_CaseO

namespace OceanPlastic

open Params

/-- **Eq. (2)–(3): the lower stages of Case O (corrected: `r_c ≤ p_m + r_p`).**
Baron–Romero–Zhang–Zhou, MSOM, doi:10.1287/msom.2022.0643, §3.2(a), eq. (2)–(3), p. 10.

Given bonuses `r_c, r_p ≥ 0` with `r_c ≤ p_m + r_p`, each collector's unique optimal volume at
acquisition price `h` is `(h + r_c) / k`; the processor's unique optimal price in
`max_{h ≥ 0} (p_m − h + r_p) q_t(h + r_c)` is `h(r_c, r_p) = (p_m + r_p − r_c) / 2`; and at that price,
with `r = r_c + r_p`, the volume, the collectors' income and the processor's profit are
`V^O(r)`, `Π^O_C(r)` and `Π^O_P(r)` of eq. (3).

**Formalization Note** The paper states this for all bonuses, which is false for
`r_c > p_m + r_p`: the printed `h` is then negative and the constrained optimum is `h = 0`.
Collectors' income is the gross payment `(h + r_c) q_t(h + r_c)`. -/
theorem eq_3 (P : Params) (rc rp : ℝ) (hrc : 0 ≤ rc) (hrp : 0 ≤ rp) (hdom : rc ≤ P.pm + rp) :
    (∀ h q : ℝ, IsMaxOn (P.collectorUtility (h + rc)) Set.univ q ↔ q = (h + rc) / P.k) ∧
    (∀ h : ℝ, P.qt (h + rc) = P.M * ((h + rc) / P.k)) ∧
    (∀ h : ℝ, (0 ≤ h ∧ IsMaxOn (P.processorObjO rc rp) (Set.Ici 0) h) ↔
      h = (P.pm + rp - rc) / 2) ∧
    P.qt ((P.pm + rp - rc) / 2 + rc) = P.VO (rc + rp) ∧
    ((P.pm + rp - rc) / 2 + rc) * P.qt ((P.pm + rp - rc) / 2 + rc) = P.PiOC (rc + rp) ∧
    P.processorObjO rc rp ((P.pm + rp - rc) / 2) = P.PiOP (rc + rp) := by sorry

end OceanPlastic
