-- Prove2me | Theorems.Thm_LongShortSI_ssi_threshold
-- name    : LongShortSI.ssi_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:51.881866+00:00
-- url     : https://prove2.me/theorems/c3e1f613-2480-4d6e-8c60-29e8465cf87e
-- title:
--   Threshold $h^{SS}_I(d)$: root of the deviation gain, and $h^{SS}_{NI}\le h^{SS}_I\le\bar h^{SS}$ (corrected: uniqueness and slope only for $d>0$; deviation profit derived)
-- statement:
--   Let $a>0$ and $0\le d<1$. At the first-period prices (8), the reseller's interior inventory $I^{SS}_{iFOC}$ and the thresholds of Tables 4 and ec5 satisfy:
--
--   1. $I^{SS}_{iFOC}(w^{SSI}_{1},w^{SSI}_{1})>0$ if and only if $h<\bar h^{SS}(d)$, with equality to $0$ at $h=\bar h^{SS}(d)$; and $h^{SS}_{NI}(d)$ solves $I^{SS}_{iFOC}(w^{LL*},w^{LL*})=0$.
--   2. The deviation price $w^{SSI}_{A1devNIA}$ maximizes supplier $A$'s deviation profit $\Pi^{SSI}_{Adev}(w_{A1})$ (the reseller holds $I_A=0$, sells (EC.6) and holds $I^{SSI}_{BdevNIA}$ of product $B$, while $B$ offers (8)); write $\Pi^{SSI}_{AdevNIA}$ for the maximum.
--   3. With $G(h)=\Pi^{SSI}_{AFOC}-\Pi^{SSI}_{AdevNIA}$:
--      (a) $G$ is convex in $h$;
--      (b) $G(h^{SS}_I(d))=0$, and for $d>0$, $h^{SS}_I(d)$ is the only root of $G$ with $h<\bar h^{SS}(d)$;
--      (c) for $d>0$, $G'(h^{SS}_I(d))<0$.
--   4. $w^{SSI}_{A1devNIA}>\bar w^{SS}_{A1}(w^{SSI}_{B1FOC})$ for every $h>h^{SS}_I(d)$.
--   5. $h^{SS}_{NI}(d)\le h^{SS}_I(d)\le\bar h^{SS}(d)$, and both inequalities are strict for $d>0$.
--
--   These facts identify $h^{SS}_I(d)$ as the holding cost below which no supplier gains by pricing the reseller out of his own inventory, the threshold that separates the two parts of Proposition 1.
--
--   Differences from the source:
--   - correction: (b) h^{SS}_I(d) "is the only solution … that satisfies h < h̄^{SS}(d)" and (c) ∂G/∂h < 0 at h^{SS}_I(d), for every d ∈ [0, 1) → both for d ∈ (0, 1); G(h^{SS}_I(d)) = 0 for every d ∈ [0, 1); reason: at d = 0, a = 1: G(h) = (4h − 1)²/68 has a double root at 1/4 = h̄^{SS}(0), so G'(1/4) = 0 and no root lies strictly below h̄^{SS}(0)
--   - correction: Π^{SSI}_{AdevNIA} printed on ec5 as (a(1 − d)(102 − d(27 + d(9 − 2d))) − (2 − d)d(6 − 9d + d³)h)/(204 − 2d(81 − d(9 + 2(4 − d)d))) → Π^{SSI}_{Adev}(w^{SSI}_{A1devNIA}), built from (EC.6), I^{SSI}_{BdevNIA} and the first branches of (EC.2) and (EC.4); reason: the printed expression repeats the deviation price; at a = 1, d = 0, h = 0 it gives 1/2, while the deviation profit is 1/8 + 1/8 = 1/4
--   - reading: "Applying FOC on Π^{SSI}_{Adev}(w_A1) … we obtain w^{SSI}_{A1devNIA}" → w^{SSI}_{A1devNIA} maximizes Π^{SSI}_{Adev} over all real w_A1; reason: Π^{SSI}_{Adev} is a concave quadratic in w_A1, so the FOC point is its maximizer
--   - generalization: h^{SS}_{NI}(d) ≤ h^{SS}_I(d) (ec5) and h̄^{SS}(d) ≥ h^{SS}_I(d) (ec6) → both, and both strict for d > 0; reason: the strict inequalities imply the printed ones; at d = 0 all three thresholds equal a/4
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), §EC.1.1–EC.1.2, p.ec5 (PDF 37); h̄^{SS} ≥ h^{SS}_I recalled on p.ec6 (PDF 38); Table 4, p.29

import Mathlib
import Definitions.Def_LongShortSI_Model
import Definitions.Def_LongShortSI_ClosedForms

open scoped NNReal

namespace LongShortSI

/-- **§EC.1.1–EC.1.2, pp.ec5–ec6 (PDF 37–38) — the threshold `h^{SS}_I(d)`** (corrected at `d = 0`).
Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20).

For `a > 0`, `d ∈ [0, 1)`:
1. at the prices (8), `I^{SS}_{iFOC} > 0` iff `h < h̄^{SS}(d)`, and `h̄^{SS}(d)` is a root;
   `h^{SS}_{NI}(d)` solves `I^{SS}_{iFOC}(w^{LL*}, w^{LL*}) = 0`;
2. `w^{SSI}_{A1devNIA}` maximizes the deviation profit `Π^{SSI}_{Adev}(w_A1)`;
3. (a) `Π^{SSI}_{AFOC} − Π^{SSI}_{AdevNIA}` is convex in `h`; (b) `h^{SS}_I(d)` is a root, and for
   `d > 0` the only root below `h̄^{SS}(d)`; (c) for `d > 0` its `h`-derivative at `h^{SS}_I(d)` is
   negative;
4. `w^{SSI}_{A1devNIA} > w̄^{SS}_{A1}(w^{SSI}_{B1FOC})` for `h > h^{SS}_I(d)`;
5. `h^{SS}_{NI}(d) ≤ h^{SS}_I(d) ≤ h̄^{SS}(d)`, both strict for `d > 0`.

**Formalization Note** At `d = 0` the two roots of the convex quadratic in 3 coincide at
`a/4 = h̄^{SS}(0)`, so its derivative vanishes there and no root lies strictly below
`h̄^{SS}(0)`: (b)'s uniqueness clause and (c) hold for `d ∈ (0, 1)` only (correction). -/
theorem ssi_threshold (a d : ℝ) (ha : 0 < a) (hd0 : 0 ≤ d) (hd1 : d < 1) :
    (∀ h, 0 < invFOC a d h (w1SSI a d h) (w1SSI a d h) ↔ h < hbarSS a d) ∧
    invFOC a d (hbarSS a d) (w1SSI a d (hbarSS a d)) (w1SSI a d (hbarSS a d)) = 0 ∧
    invFOC a d (hSSNI a d) (wLL a d) (wLL a d) = 0 ∧
    (∀ h w, devProfit a d h w ≤ devProfit a d h (wDev a d h)) ∧
    ConvexOn ℝ Set.univ (fun h => PiFOC a d h - PiDev a d h) ∧
    PiFOC a d (hSSI a d) - PiDev a d (hSSI a d) = 0 ∧
    (0 < d → ∀ h, h < hbarSS a d → PiFOC a d h - PiDev a d h = 0 → h = hSSI a d) ∧
    (0 < d → deriv (fun h => PiFOC a d h - PiDev a d h) (hSSI a d) < 0) ∧
    (∀ h, hSSI a d < h → wbarSS1 a d h (w1SSI a d h) < wDev a d h) ∧
    hSSNI a d ≤ hSSI a d ∧ hSSI a d ≤ hbarSS a d ∧
    (0 < d → hSSNI a d < hSSI a d ∧ hSSI a d < hbarSS a d) := by sorry

end LongShortSI
