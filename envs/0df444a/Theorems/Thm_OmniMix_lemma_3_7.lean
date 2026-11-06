-- Prove2me | Theorems.Thm_OmniMix_lemma_3_7
-- name    : OmniMix.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:40:41.135728+00:00
-- url     : https://prove2.me/theorems/29724d92-80aa-4e0f-aa88-373bec463dc4
-- title:
--   Lemma 3.7 — clipping cost and Eq. (26) (corrected: ℓ finite on (0,1))
-- statement:
--   Let $0<\delta<1/2$, $\beta>0$, and let $\ell$ be a proper $\beta$-mixable loss, never $-\infty$ and finite on $(0,1)$. For every $q\in[0,1]$ and $y\in\{0,1\}$:
--   1. $\displaystyle \ell(\mathrm{clip}(q,I_\delta),y)-\ell(q,y)\le\frac{-\log(1-\delta)}{\beta}$;
--   2. $\displaystyle \frac{-\log(1-\delta)}{\beta}\le\frac{2\delta}{\beta}$;
--   3. for every density $w$ of a V-shaped representation of $\ell$ and every $p\in I_\delta$,
--   $$
--   \ell(p,y)-\ell(q,y)\le\int_{I_\delta}w(v)\big[b_v(p,q)(y-p)-d_v(p,q)\big]\,dv+\frac{2\delta}{\beta}.\tag{26}
--   $$
--   Loss differences are extended-real: if $\ell(q,y)=+\infty$ the left sides are $-\infty$.
--
--   Since Algorithm 2 forecasts only in $I_\delta$, (26) shows that comparing with clipped benchmarks, and using thresholds in $I_\delta$ only, costs $O(\delta/\beta)$ per round.
--
--   Differences from the source:
--   - generalization: δ = 1/(2(T+1)) → every δ ∈ (0, 1/2); reason: the proof uses only δ < 1/2; the paper's δ is one instance
--   - correction: β-mixable proper loss → also finite on (0,1) and never −∞; reason: same correction as Lemma 2.1: ℓ(q,0) = q, ℓ(q,1) = +∞ is proper and mixable but has no representation (13) with real C_ℓ, on which this result's proof rests; −∞ is outside the paper's codomain
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Lemma 3.7, p.15 (PDF p.17), Eq. (26); proof App. B, pp.31–32

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsMixable
import Definitions.Def_OmniMix_HasVRep
import Definitions.Def_OmniMix_Idelta
import Definitions.Def_OmniMix_clip
import Definitions.Def_OmniMix_dV
import Definitions.Def_OmniMix_outVal

namespace OmniMix

/-- **Lemma 3.7 (clipping cost) and Eq. (26).** Liu–Luo–Ratliff, arXiv:2610.41023, §3.2, p.15 (proof App. B, pp.31–32): "For any
β-mixable proper loss `ℓ`, `q ∈ [0, 1]`, and `y ∈ {0, 1}`,
`ℓ(clip(q, I_δ), y) − ℓ(q, y) ≤ −log(1 − δ)/β ≤ 2δ/β`, where we recall
`clip(q, I_δ) = min{1 − δ, max{δ, q}}`. Consequently, for every `p ∈ I_δ`,
`ℓ(p, y) − ℓ(q, y) ≤ ∫_{I_δ} w_ℓ(v)[b_v(p, q)(y − p) − d_v(p, q)] dv + 2δ/β`. (26)"

Stated for every `δ ∈ (0, 1/2)`; the three conjuncts are the two inequalities of the first display
and (26) for the density `w` of any representation (13).

**Formalization Note.** Loss differences are in `EReal`: when `ℓ(q,y) = +∞` the left sides are `−∞`
("the corresponding loss difference is −∞", p.31). The loss is also assumed finite on `(0,1)` and
never `−∞`, the correction of Lemma 2.1. -/
theorem lemma_3_7 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (β : ℝ) (hβ : 0 < β) (ℓ : Loss)
    (hprop : IsProper ℓ) (hbot : ∀ p y, ℓ p y ≠ ⊥) (hfin : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤) (hmix : IsMixable β ℓ)
    (q : unitInterval) (y : Bool) :
    ℓ (clip δ q) y - ℓ q y ≤ ((-Real.log (1 - δ) / β : ℝ) : EReal) ∧
    -Real.log (1 - δ) / β ≤ 2 * δ / β ∧
    ∀ (C : Bool → ℝ) (w : ℝ → ENNReal), HasVRep ℓ C w → ∀ p : unitInterval, (p : ℝ) ∈ Idelta δ →
      ℓ p y - ℓ q y ≤ (((∫ v in Idelta δ,
        (w v).toReal * (bV v p q * (outVal y - p) - dV v p q)) + 2 * δ / β : ℝ) : EReal) := by sorry

end OmniMix
