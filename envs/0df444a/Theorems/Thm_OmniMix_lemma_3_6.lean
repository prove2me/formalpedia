-- Prove2me | Theorems.Thm_OmniMix_lemma_3_6
-- name    : OmniMix.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:40:27.305791+00:00
-- url     : https://prove2.me/theorems/c532d7e4-eb8f-4403-9190-e65c27cf6547
-- title:
--   Lemma 3.6 — variance term versus properness gain
-- statement:
--   Let $0<\delta<1/2$, $\beta>0$, and let $\ell$ be a proper $\beta$-mixable loss with a V-shaped representation $\ell(p,y)=C(y)+\int_0^1w(v)\lambda_v(p,y)\,dv$ ($C$ real, $w\ge0$ measurable). For every $\eta\in(0,1/2]$, $p\in I_\delta$ and $q\in[0,1]$,
--   $$
--   \int_{I_\delta}w(v)\big[\eta p(1-p)\,b_v(p,q)^2-d_v(p,q)\big]\,dv\le\frac{\eta^2}{\beta}.
--   $$
--
--   The extra factor $p(1-p)$ in the variance term offsets the curvature $1/(\beta v(1-v))$ allowed for mixable losses, leaving a term of order $\eta^2$.
--
--   Differences from the source:
--   - generalization: δ = 1/(2(T+1)), the standing δ of §3.2 → every δ ∈ (0, 1/2); reason: the proof never uses the value of δ; the paper's δ is one instance
--   - reading: w_ℓ, the density of Lemma 2.1 → w, the density of any representation (13) with real constants; reason: the density is unique a.e.; a mixable loss with such a representation is never −∞ and finite on (0,1) (real C_ℓ(0) = ℓ(0,0), C_ℓ(1) = ℓ(1,1), and properness plus mixability exclude an interior +∞), so the correction of Lemma 2.1 is carried by this hypothesis
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Lemma 3.6, p.15 (PDF p.17); proof App. B, p.31

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsMixable
import Definitions.Def_OmniMix_HasVRep
import Definitions.Def_OmniMix_Idelta
import Definitions.Def_OmniMix_dV

namespace OmniMix

/-- **Lemma 3.6.** Liu–Luo–Ratliff, arXiv:2610.41023, §3.2, p.15 (proof App. B, p.31): "For any β-mixable proper loss `ℓ`,
`η ∈ (0, 1/2]`, `p ∈ I_δ`, and `q ∈ [0, 1]`, we have
`∫_{I_δ} w_ℓ(v)[ηp(1 − p)b_v(p, q)² − d_v(p, q)] dv ≤ η²/β`."

Stated for every `δ ∈ (0, 1/2)` (the paper's `δ = 1/(2(T+1))` is one of them), and for the density
`w` of any representation (13) of `ℓ`.

**Formalization Note.** A representation (13) with real constants already makes `ℓ` never `−∞`
and, with mixability, finite on `(0,1)`, so the correction of Lemma 2.1 needs no separate
hypothesis here. On `I_δ` with `δ > 0` the integrand is integrable (by the curvature bound of Lemma 2.1),
so the Bochner integral is the paper's. -/
theorem lemma_3_6 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (β : ℝ) (hβ : 0 < β) (ℓ : Loss)
    (hprop : IsProper ℓ) (hmix : IsMixable β ℓ)
    (C : Bool → ℝ) (w : ℝ → ENNReal) (hrep : HasVRep ℓ C w) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) (p : unitInterval) (hp : (p : ℝ) ∈ Idelta δ) (q : unitInterval) :
    ∫ v in Idelta δ, (w v).toReal * (η * p * (1 - p) * bV v p q ^ 2 - dV v p q) ≤ η ^ 2 / β := by sorry

end OmniMix
