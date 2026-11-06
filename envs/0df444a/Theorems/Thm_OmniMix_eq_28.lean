-- Prove2me | Theorems.Thm_OmniMix_eq_28
-- name    : OmniMix.eq_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:40:04.78437+00:00
-- url     : https://prove2.me/theorems/86ef0711-2055-4927-853f-86413238d6ac
-- title:
--   Eq. (28) — central condition $\mathbb E_{Y\sim\mathrm{Ber}(p)}e^{\beta(\ell(p,Y)-\ell(q,Y))}\le1$ (corrected: ℓ finite on (0,1))
-- statement:
--   Let $\ell$ be a proper loss, never $-\infty$ and finite on $(0,1)$, and let $\beta>0$ be such that $\ell$ is $\beta$-mixable. For every $p\in(0,1)$ and $q\in[0,1]$,
--   $$
--   \mathbb E_{Y\sim\mathrm{Ber}(p)}\Big[\exp\big(\beta(\ell(p,Y)-\ell(q,Y))\big)\Big]
--   =(1-p)\,e^{\beta(\ell(p,0)-\ell(q,0))}+p\,e^{\beta(\ell(p,1)-\ell(q,1))}\le1,
--   $$
--   with $e^{-\infty}=0$ when $\ell(q,y)=+\infty$.
--
--   This is the central condition of van Erven et al.; Lemma 3.7 applies it at $p=\delta$ and $p=1-\delta$ to bound the cost of clipping benchmark predictions.
--
--   Differences from the source:
--   - generalization: β⋆_ℓ, the largest mixability constant → every β > 0 at which ℓ is β-mixable; reason: at β = β⋆_ℓ (when it is attained) this is the page's inequality
--   - correction: β-mixable proper loss → also finite on (0,1) and never −∞; reason: same correction as Lemma 2.1: ℓ(q,0) = q, ℓ(q,1) = +∞ is proper and mixable but has no representation (13) with real C_ℓ, on which this result's proof rests; −∞ is outside the paper's codomain
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Lemma 3.8 proof, §3.3, p.17 (PDF p.19), Eq. (28)

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsMixable

namespace OmniMix

/-- **Central condition, Eq. (28).** Liu–Luo–Ratliff, arXiv:2610.41023, §3.3, p.17 (proof of Lemma 3.8): "it suffices to show
`E_{Y∼Ber(p)}[exp(β⋆_ℓ(ℓ(p, Y) − ℓ(q, Y)))] ≤ 1`, (28) which is exactly the central condition of
[VEGM+15] and is implied by mixability"; the statement there is for "any mixable proper loss `ℓ`,
`y ∈ {0, 1}`, `p ∈ (0, 1)` and `q ∈ [0, 1]`".

Stated for every `β > 0` at which `ℓ` is β-mixable, for a proper loss that is never `−∞` and finite
on `(0,1)`:
`(1 − p)·exp(β(ℓ(p,0) − ℓ(q,0))) + p·exp(β(ℓ(p,1) − ℓ(q,1))) ≤ 1`.

**Formalization Note.** Computed in `ℝ≥0∞` with `EReal.exp`; when `ℓ(q,y) = +∞` the difference is
`−∞` and its exponential is `0`. The finiteness on `(0,1)` is the correction of Lemma 2.1 and
Theorem 1.2. -/
theorem eq_28 (ℓ : Loss) (β : ℝ) (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥) (hfin : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤) (hmix : IsMixable β ℓ)
    (p q : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ENNReal.ofReal (1 - p) * EReal.exp ((β : EReal) * (ℓ p false - ℓ q false)) +
      ENNReal.ofReal p * EReal.exp ((β : EReal) * (ℓ p true - ℓ q true)) ≤ 1 := by sorry

end OmniMix
