-- Prove2me | Theorems.Thm_LongShortSI_hhat_threshold
-- name    : LongShortSI.hhat_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:49.118496+00:00
-- url     : https://prove2.me/theorems/eebbeaa7-fa01-40e3-abf3-94bb059d8a7c
-- title:
--   §EC.3.1 — the supplier threshold $\widehat h(d)$ and $\widehat d$ (corrected: slope claim only for $d>0$)
-- statement:
--   Let $f_d(h)=\Pi^{SS*}_i-\Pi^{LL*}_i$, the difference of Table 2's SSI and LL rows $\Pi^*_i$, as a function of the holding cost $h$, and let $\widehat h(d)$ be Table 4's threshold. There is $\widehat d\in(0,1)$ such that for every $a>0$:
--
--   1. for every $d\in[0,1)$: $f_d$ is strictly convex; $f_d(\widehat h(d))=0$; $\widehat h(d)\le h^{SS}_I(d)$, strictly for $d>0$; for $d>0$, $f_d'(\widehat h(d))<0$; $f_d(h)>0$ for all $h<\widehat h(d)$; and $f_d(h)<0$ for $\widehat h(d)<h<h^{SS}_I(d)$;
--   2. $\widehat h'(0)<0$ and $\widehat h(0)=h^{SS}_I(0)>0$;
--   3. $\widehat h(\widehat d)=0$ and $\widehat h(d)<0$ for $d\in(\widehat d,1)$;
--   4. for $d\in(\widehat d,1)$, $\Pi^{SS*}_i<\Pi^{LL*}_i$ for every $0\le h<h^{SS}_I(d)$.
--
--   This is the closed-form core of Proposition 3(i): below $\widehat h(d)$ the suppliers gain from short-term contracts, between $\widehat h(d)$ and $h^{SS}_I(d)$ they lose, and for $d>\widehat d$ (numerically $\widehat d\approx0.44$) they lose at every holding cost.
--
--   Differences from the source:
--   - correction: ∂(Π^{SS*}_i − Π^{LL*}_i)/∂h at h = ĥ(d) is negative, for every d ∈ [0, 1) → for d ∈ (0, 1); reason: at d = 0, a = 1: f_0(h) = (4h − 1)²/68 has a double root at ĥ(0) = 1/4, so the derivative there is 0
--   - generalization: the paragraph proves f_d > 0 below ĥ(d) and f_d < 0 everywhere on [0, h^{SS}_I(d)) for d > d̂ → also f_d(h) < 0 for ĥ(d) < h < h^{SS}_I(d), every d ∈ [0, 1); reason: this is the middle clause of Proposition 3(i), which the paragraph's argument leaves implicit (the second root of f_d lies above h^{SS}_I(d)); it adds to the printed claims
--   - encoding: ∂ĥ(d)/∂d at d = 0, and d̂ a function of d alone → the two-sided derivative of the formula ĥ (defined for all real d) at 0; d̂ chosen before a; reason: the formula is smooth near d = 0; ĥ is proportional to a, so its zero does not depend on a
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), §EC.3.1, p.ec6 (PDF 38); Table 2 rows Π*_i, p.28; Tables 4–5 (ĥ, Q, Y), p.29

import Mathlib
import Definitions.Def_LongShortSI_Model
import Definitions.Def_LongShortSI_ClosedForms

open scoped NNReal
open Filter Topology

namespace LongShortSI

/-- **§EC.3.1, p.ec6 (PDF 38) — the supplier threshold `ĥ(d)`** (corrected at `d = 0`).
Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20).

There is `d̂ ∈ (0, 1)` such that for every `a > 0`, with `f_d(h) = Π^{SS*}_i − Π^{LL*}_i`
(Table 2's SSI and LL rows `Π*_i`):
1. for `d ∈ [0, 1)`: `f_d` is strictly convex in `h`; `f_d(ĥ(d)) = 0`; `ĥ(d) ≤ h^{SS}_I(d)`, strict
   for `d > 0`; for `d > 0` the derivative of `f_d` at `ĥ(d)` is negative; `f_d(h) > 0` for
   `h < ĥ(d)`, and `f_d(h) < 0` for `ĥ(d) < h < h^{SS}_I(d)`;
2. `ĥ'(0) < 0` and `ĥ(0) = h^{SS}_I(0) > 0`;
3. `ĥ(d̂) = 0` and `ĥ(d) < 0` for `d ∈ (d̂, 1)`;
4. for `d ∈ (d̂, 1)`, `f_d(h) < 0` for every `0 ≤ h < h^{SS}_I(d)`.

**Formalization Note** At `d = 0`, `f_0` has a double root at `a/4 = ĥ(0)`, so the printed
derivative claim holds for `d > 0` only (correction). The clause `f_d < 0` on
`(ĥ(d), h^{SS}_I(d))` is Proposition 3(i)'s, which this paragraph's argument leaves implicit. -/
theorem hhat_threshold :
    ∃ dhat : ℝ, 0 < dhat ∧ dhat < 1 ∧ ∀ a : ℝ, 0 < a →
      (∀ d, 0 ≤ d → d < 1 →
        StrictConvexOn ℝ Set.univ (fun h => PiSSI a d h - PiLL a d) ∧
        PiSSI a d (hhat a d) - PiLL a d = 0 ∧
        hhat a d ≤ hSSI a d ∧ (0 < d → hhat a d < hSSI a d) ∧
        (0 < d → deriv (fun h => PiSSI a d h - PiLL a d) (hhat a d) < 0) ∧
        (∀ h, h < hhat a d → PiLL a d < PiSSI a d h) ∧
        (∀ h, hhat a d < h → h < hSSI a d → PiSSI a d h < PiLL a d)) ∧
      deriv (fun d => hhat a d) 0 < 0 ∧ hhat a 0 = hSSI a 0 ∧ 0 < hSSI a 0 ∧
      hhat a dhat = 0 ∧ (∀ d, dhat < d → d < 1 → hhat a d < 0) ∧
      (∀ d, dhat < d → d < 1 → ∀ h, 0 ≤ h → h < hSSI a d → PiSSI a d h < PiLL a d) := by sorry

end LongShortSI
