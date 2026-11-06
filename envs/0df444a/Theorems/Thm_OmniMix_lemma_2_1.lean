-- Prove2me | Theorems.Thm_OmniMix_lemma_2_1
-- name    : OmniMix.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:39:59.775199+00:00
-- url     : https://prove2.me/theorems/1d0cc179-8c88-4eb1-95ea-b9fa92e7a443
-- title:
--   Lemma 2.1 — V-shaped representation and curvature bounds (corrected: mixable ℓ finite on (0,1) and continuous at 0, 1)
-- statement:
--   Recall the V-shaped losses $\lambda_v(q,1)=(1-v)\mathbb I\{q<v\}$, $\lambda_v(q,0)=v\mathbb I\{q\ge v\}$. Let $\lambda$ denote Lebesgue measure on $[0,1]$.
--
--   1. **Representation.** Let $\ell$ be a proper loss that is either $L$-Lipschitz for some $L$, or $\beta$-mixable for some $\beta>0$, never $-\infty$, finite on $(0,1)$, and with both partial losses $\ell(\cdot,y)$ continuous (in $\mathbb R\cup\{+\infty\}$) at $0$ and at $1$. Then there are real constants $C(0),C(1)$ and a measurable $w:\mathbb R\to[0,\infty]$ with
--   $$
--   \ell(p,y)=C(y)+\int_0^1 w(v)\lambda_v(p,y)\,dv\qquad(p\in[0,1],\ y\in\{0,1\}).\tag{13}
--   $$
--   2. **Lipschitz curvature.** For every proper loss admitting (13) and every $L>0$: $\ell$ is $L$-Lipschitz if and only if $w(v)\le L/\max\{v,1-v\}$ for $\lambda$-a.e. $v$.
--   3. **Mixability curvature.** For every proper loss admitting (13) and every $\beta>0$: $\ell$ is $\beta$-mixable if and only if $w(v)\le 1/(\beta v(1-v))$ for $\lambda$-a.e. $v$.
--   4. **Consequence.** If a proper loss $\ell$ is $L$-Lipschitz with $L>0$, then every density $w$ of a representation (13) satisfies $w(v)\le 2L$ a.e., and $\ell$ is $2/L$-mixable.
--
--   The representation reduces every Lipschitz or mixable proper loss to a nonnegative mixture of threshold losses, and the curvature bounds turn Lipschitzness and mixability into pointwise bounds on the density, which is how the paper's algorithms handle all such losses at once.
--
--   Differences from the source:
--   - correction: every mixable proper loss → ℓ also finite on (0,1) and never −∞; reason: ℓ(q,0) = q, ℓ(q,1) = +∞ is proper and β-mixable for every β, yet (13) with real C_ℓ fails at p = 1 and Theorem 1.2's bound (0 at β⋆ = +∞) fails with F = {0,1}; −∞ is outside the paper's codomain ℝ∪{+∞}
--   - encoding: Lipschitz loss with |ℓ(p,y) − ℓ(q,y)| ≤ L|p − q| → both partial losses real-valued and L-Lipschitz; reason: the absolute difference presupposes finite values
--   - encoding: C_ℓ(y) independent of the prediction, w_ℓ nonnegative measurable, integral ∫_0^1 → C : {0,1} → ℝ, w measurable into [0,∞], lower Lebesgue integral over [0,1] coerced to ℝ∪{±∞}; reason: the proof's C_ℓ(y) = (1−y)ℓ(0,0)+yℓ(1,1) is finite; the integral may be +∞ at the endpoints
--   - reading: "ℓ is Lipschitz" in the first part → ℓ is L-Lipschitz for some L; reason: the paper's L_Lip(L) for an unspecified L
--   - correction: every mixable proper loss → ℓ(·,0), ℓ(·,1) also continuous in ℝ∪{±∞} at 0 and 1; reason: the proof (App. C, p.33) passes to endpoint limits by an "endpoint convention in Section 2" that §2 never states; squared loss with ℓ(0,1) raised to +∞ is proper, 2-mixable, finite on (0,1) and never −∞, yet (13) forces w = 2 a.e. and ℓ(0,1) = 1
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Lemma 2.1, p.9 (PDF p.11), Eq. (13); proof App. C, pp.32–34

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsMixable
import Definitions.Def_OmniMix_IsLipschitzLoss
import Definitions.Def_OmniMix_HasVRep

namespace OmniMix

/-- **Lemma 2.1 (V-shaped representation and curvature bounds).** Liu–Luo–Ratliff, arXiv:2610.41023, §2, p.9 (proof App. C,
pp.32–34): "If a proper loss `ℓ` is Lipschitz or mixable, then it can be written as
`ℓ(p, y) = C_ℓ(y) + ∫_0^1 w_ℓ(v)λ_v(p, y) dv` (13) for all `p ∈ [0, 1]` and `y ∈ {0, 1}`, where `C_ℓ(y)`
is independent of the prediction and `w_ℓ` is nonnegative and measurable. Moreover, for any proper
loss admitting the representation Eq. (13) and any `L, β > 0`,
• `ℓ ∈ L_Lip(L)` if and only if `w_ℓ(v) ≤ L/max{v, 1−v}` almost everywhere;
• `ℓ ∈ L_mix(β)` if and only if `w_ℓ(v) ≤ 1/(βv(1−v))` almost everywhere.
Consequently, if `ℓ ∈ L_Lip(L)`, then `w_ℓ(v) ≤ 2L` almost everywhere and also `ℓ ∈ L_mix(2/L)`."

The four conjuncts are: the representation; the Lipschitz iff; the mixability iff; the consequence.

**Formalization Note.** Correction: in the first part a mixable loss is also assumed finite on
`(0,1)` and never `−∞` (the paper's codomain). Without finiteness the representation with a real
`C_ℓ` fails for `ℓ(q,0) = q`, `ℓ(q,1) = +∞`, which is proper and β-mixable for every β: (13) at
`p = 1` gives `ℓ(1,1) = C_ℓ(1)`. Correction: the mixable loss is also assumed continuous (in
`ℝ ∪ {±∞}`) at the endpoints `0` and `1`, the "endpoint convention" the proof invokes (App. C, p.33:
"Passing to these endpoint limits … The equalities extend to `p = 0, 1` by the same endpoint
convention") but that §2 never states. Without it the representation fails for squared loss with
`ℓ(0,1)` raised to `+∞`: it is proper, 2-mixable, finite on `(0,1)` and never `−∞`, but (13) forces
`w = 2` a.e. (from `ℓ(·,0) = p²`), hence `ℓ(0,1) = C_ℓ(1) + ∫_0^1 2(1−v) dv = 1`. A Lipschitz loss is
real-valued and continuous by definition. Almost everywhere is for Lebesgue measure on `[0,1]`. -/
theorem lemma_2_1 :
    (∀ ℓ : Loss, IsProper ℓ →
      ((∃ L : ℝ, IsLipschitzLoss L ℓ) ∨
        ((∀ p y, ℓ p y ≠ ⊥) ∧ (∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤) ∧
          (∀ y, ContinuousAt (fun p : unitInterval => ℓ p y) 0 ∧
            ContinuousAt (fun p : unitInterval => ℓ p y) 1) ∧
          ∃ β : ℝ, 0 < β ∧ IsMixable β ℓ)) →
      ∃ (C : Bool → ℝ) (w : ℝ → ENNReal), HasVRep ℓ C w) ∧
    (∀ (ℓ : Loss) (C : Bool → ℝ) (w : ℝ → ENNReal), IsProper ℓ → HasVRep ℓ C w →
      ∀ L : ℝ, 0 < L → (IsLipschitzLoss L ℓ ↔
        ∀ᵐ v ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
          w v ≤ ENNReal.ofReal (L / max v (1 - v)))) ∧
    (∀ (ℓ : Loss) (C : Bool → ℝ) (w : ℝ → ENNReal), IsProper ℓ → HasVRep ℓ C w →
      ∀ β : ℝ, 0 < β → (IsMixable β ℓ ↔
        ∀ᵐ v ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
          w v ≤ ENNReal.ofReal (1 / (β * v * (1 - v))))) ∧
    (∀ (ℓ : Loss) (L : ℝ), IsProper ℓ → 0 < L → IsLipschitzLoss L ℓ →
      (∀ (C : Bool → ℝ) (w : ℝ → ENNReal), HasVRep ℓ C w →
        ∀ᵐ v ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)), w v ≤ ENNReal.ofReal (2 * L)) ∧
      IsMixable (2 / L) ℓ) := by sorry

end OmniMix
