-- Prove2me | Theorems.Thm_OmniMix_eq_15
-- name    : OmniMix.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:40:31.550208+00:00
-- url     : https://prove2.me/theorems/1c22c111-866b-4465-8e91-eccd985e5914
-- title:
--   Eq. (15) — regret identity for a loss with V-shaped representation
-- statement:
--   Let $\ell$ be a loss with a V-shaped representation $\ell(p,y)=C(y)+\int_0^1 w(v)\lambda_v(p,y)\,dv$ (constants $C$ real, density $w\ge0$ measurable). For all $p,q\in[0,1]$ and $y\in\{0,1\}$ with $\ell(p,y)$ and $\ell(q,y)$ not both $+\infty$,
--   $$
--   \ell(p,y)-\ell(q,y)=\int_0^1 w(v)\big(b_v(p,q)(y-p)-d_v(p,q)\big)\,dv\tag{15}
--   $$
--   in $\mathbb R\cup\{\pm\infty\}$, where the integral is that of the positive part minus that of the negative part (the integrand has one sign, so one of them is $0$). When $\ell(p,y)$ and $\ell(q,y)$ are both finite, the integrand is moreover integrable on $[0,1]$ and (15) holds with the real integral.
--
--   This identity writes every loss difference as a weighted sum of threshold test terms; the algorithms of the paper control the right side threshold by threshold.
--
--   Differences from the source:
--   - generalization: ℓ Lipschitz or mixable (so that (13) holds) → any loss with a representation (13); reason: Lemma 2.1 supplies the representation for every (corrected) Lipschitz or mixable proper loss
--   - encoding: for any p, q ∈ [0,1] and y → for p, q, y with ℓ(p,y), ℓ(q,y) not both +∞, the integral read as positive part minus negative part in ℝ∪{±∞}; reason: ℓ(p,y) = ℓ(q,y) = +∞ is the undefined ∞ − ∞ (log loss at p = q = 0, y = 1); a single infinite value gives ±∞ on both sides
--   - encoding: the integral ∫_0^1 w_ℓ(·)(…) → in addition, for finite ℓ(p,y), ℓ(q,y), integrability on [0,1] asserted and the real value of w used; reason: the real integral is the paper's when both sides are finite; w is finite a.e. where the integrand is nonzero
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.10 (PDF p.12), Eq. (15)

import Mathlib
import Definitions.Def_OmniMix_HasVRep
import Definitions.Def_OmniMix_bV
import Definitions.Def_OmniMix_dV
import Definitions.Def_OmniMix_outVal

namespace OmniMix

/-- **Regret identity, Eq. (15).** Liu–Luo–Ratliff, arXiv:2610.41023, §2, p.10: "when `ℓ` is either Lipschitz or mixable, Eq. (13)
and Eq. (14) together imply: for any `p, q ∈ [0, 1]` and `y ∈ {0, 1}`,
`ℓ(p, y) − ℓ(q, y) = ∫_0^1 w_ℓ(v)(b_v(p, q)(y − p) − d_v(p, q)) dv`, (15)".

Stated for every loss with a representation (13) (constants `C`, density `w`). First conjunct: for
`p, q, y` with `ℓ(p,y)` and `ℓ(q,y)` not both `+∞`, the identity holds in `ℝ ∪ {±∞}`, the integral
being the integral of the positive part minus that of the negative part (the integrand has one sign
on `[0,1]`, so one of the two is `0`). Second conjunct: when both values are finite, the integrand is
integrable on `[0,1]` and the identity holds with the real (Bochner) integral.

**Formalization Note.** The premise "Lipschitz or mixable" is replaced by its consequence, the
representation (13) (Lemma 2.1). Only `ℓ(p,y) = ℓ(q,y) = +∞` is excluded, the undefined `∞ − ∞`
(e.g. log loss at `p = q = 0`, `y = 1`); a finite minus an infinite loss is `−∞` on both sides
(the paper's convention, p.31). `w` is `ℝ≥0∞`-valued; in the second conjunct `(w v).toReal` is its
real value, which agrees with `w` almost everywhere where the integrand is nonzero. -/
theorem eq_15 (ℓ : Loss) (C : Bool → ℝ) (w : ℝ → ENNReal) (hrep : HasVRep ℓ C w)
    (p q : unitInterval) (y : Bool) :
    ((ℓ p y ≠ ⊤ ∨ ℓ q y ≠ ⊤) →
      ℓ p y - ℓ q y =
        ((∫⁻ v in Set.Icc (0 : ℝ) 1,
            w v * ENNReal.ofReal (bV v p q * (outVal y - p) - dV v p q) : ENNReal) : EReal) -
          ((∫⁻ v in Set.Icc (0 : ℝ) 1,
            w v * ENNReal.ofReal (-(bV v p q * (outVal y - p) - dV v p q)) : ENNReal) : EReal)) ∧
    (ℓ p y ≠ ⊤ → ℓ q y ≠ ⊤ →
      MeasureTheory.IntegrableOn
        (fun v => (w v).toReal * (bV v p q * (outVal y - p) - dV v p q)) (Set.Icc (0 : ℝ) 1) ∧
      ℓ p y - ℓ q y = ((∫ v in Set.Icc (0 : ℝ) 1,
        (w v).toReal * (bV v p q * (outVal y - p) - dV v p q) : ℝ) : EReal)) := by sorry

end OmniMix
