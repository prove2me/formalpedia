-- Prove2me | Theorems.Thm_LongShortSI_reseller_large_d
-- name    : LongShortSI.reseller_large_d
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:00.495132+00:00
-- url     : https://prove2.me/theorems/4462117a-14c1-451c-acbf-211e166c5b0b
-- title:
--   §EC.3.2 — the reseller prefers short-term contracts for large $d$: slope $-a/36$ at $\bar h^{SS}$
-- statement:
--   Let $g_d(h)=\pi^{SS*}-\pi^{LL*}$, the difference of Table 2's SSI and LL rows $\pi^*$, as a function of $h$. Then for every $a>0$:
--
--   1. for every $d\in[0,1)$, $g_d$ is convex in $h$ and $\bar h^{SS}(d)\ge h^{SS}_I(d)$;
--   2. $\displaystyle\lim_{d\to1^-}\ g_d'\bigl(\bar h^{SS}(d)\bigr)=-\frac{a}{36}$;
--
--   and there is $d_2\in(0,1)$, not depending on $a$, such that for every $d\in(d_2,1)$ and every $0\le h<h^{SS}_I(d)$,
--   $$
--   \pi^{SS*}>\pi^{LL*}:
--   $$
--   when products are close substitutes, the reseller prefers short-term contracts at every holding cost low enough to induce inventory.
--
--   This is the closed-form core of Proposition 3(ii); numerically the reseller prefers short-term contracts at all such holding costs once $d$ exceeds about $0.3$.
--
--   Differences from the source:
--   - reading: "as d becomes sufficiently high, the reseller prefers SS contracts for all holding costs low enough to induce inventory to be held" → ∃ d₂ ∈ (0, 1), chosen before a, such that π^{SS*} > π^{LL*} for every d ∈ (d₂, 1) and 0 ≤ h < h^{SS}_I(d); reason: "sufficiently high" is an existential threshold below 1; π^{SS*} − π^{LL*} scales with a², so the threshold does not depend on a; the conclusion does not follow from the limit alone and is stated separately
--   - encoding: lim_{d→1} → limit along d → 1 from below; reason: d ∈ [0, 1) is the model's domain
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), §EC.3.2, p.ec6 (PDF 38); Table 2 rows π*, p.28; Table 5 (X), p.29

import Mathlib
import Definitions.Def_LongShortSI_Model
import Definitions.Def_LongShortSI_ClosedForms

open scoped NNReal
open Filter Topology

namespace LongShortSI

/-- **§EC.3.2, p.ec6 (PDF 38) — the reseller prefers SS for large `d`.**
Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20).

With `g_d(h) = π^{SS*} − π^{LL*}` (Table 2's SSI and LL rows `π*`): `g_d` is convex in `h`;
`h̄^{SS}(d) ≥ h^{SS}_I(d)`; `lim_{d→1} g_d'(h̄^{SS}(d)) = −a/36`; and there is `d₂ ∈ (0, 1)`, not
depending on `a`, such that for `d ∈ (d₂, 1)` the reseller strictly prefers SS,
`g_d(h) > 0`, at every `0 ≤ h < h^{SS}_I(d)`.

**Formalization Note** The limit is taken as `d → 1⁻`. The last clause is the conclusion the
paragraph draws ("as d becomes sufficiently high, the reseller prefers SS contracts for all holding
costs low enough to induce inventory to be held"); it does not follow from the limit alone and is
stated separately. -/
theorem reseller_large_d :
    ∃ d2 : ℝ, 0 < d2 ∧ d2 < 1 ∧ ∀ a : ℝ, 0 < a →
      (∀ d, 0 ≤ d → d < 1 →
        ConvexOn ℝ Set.univ (fun h => piSSI a d h - piLL a d) ∧ hSSI a d ≤ hbarSS a d) ∧
      Tendsto (fun d => deriv (fun h => piSSI a d h - piLL a d) (hbarSS a d)) (𝓝[<] 1)
        (𝓝 (-a / 36)) ∧
      (∀ d, d2 < d → d < 1 → ∀ h, 0 ≤ h → h < hSSI a d → piLL a d < piSSI a d h) := by sorry

end LongShortSI
