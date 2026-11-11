-- Prove2me | Theorems.Thm_GoldProxGap_lemma_5_8
-- name    : GoldProxGap.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:04.964843+00:00
-- url     : https://prove2.me/theorems/eb211f35-508f-4c72-8bd9-87e6083c68ba
-- title:
--   Lemma 5.8 — moment equations and the coefficients of $J$: $M_1=\dots=M_{t-1}=0\iff J_1=\dots=J_{t-1}=0\iff\deg J\le N/2^t$, and $J=\hat J^{2^t}$
-- statement:
--   **Lemma 5.8 (Moment equations and the coefficients of $J$).** In the setting of (5.2), write $J=\sum_{i=0}^{d-1}J_iX^{2^i}$. Then $J_0=0$, and for $2\le t\le d/2$ the following are equivalent:
--   1. $M_1(A)=\dots=M_{t-1}(A)=0$;
--   2. $J_1=\dots=J_{t-1}=0$;
--   3. $J_{d-t+1}=\dots=J_{d-1}=0$, that is, $\deg J\le N/2^t$.
--
--   When they hold,
--   $$
--   J=\sum_{i=t}^{d-t}J_iX^{2^i}=\hat J^{2^t},\qquad \hat J=\sum_{i=t}^{d-t}J_i^{2^{-t}}X^{2^{i-t}},\qquad \deg\hat J\le\frac N{2^{2t}},
--   $$
--   where $a^{2^{-t}}$ is the $2^t$-th root of $a$ in $\mathbb B$.
--
--   The lemma translates the Gold moment equations into a degree bound on $Q'$, which is how the rank-$2t$ matrices produce polynomials of the right degree.
--
--   **Formalization Note** $J_i$ is the coefficient of $X^{2^i}$; the representation $J=\sum_{i<d}J_iX^{2^i}$ is stated as a conclusion. Degrees are in `WithBot ℕ`.
--
--   Differences from the source:
--   - encoding: a basis ω₁, …, ω_d of the label space D̂ → a coordinate basis φs of the linear functions D → F₂ with ω_i = label(φs i); reason: by Lemma 5.5(2) the label map is an F₂-linear bijection, so this is the same data
--   - encoding: "Write J = Σ_{i=0}^{d−1} J_i X^{2^i}" → a conclusion J = Σ_{i<d} J_i X^{2^i} with J_i the coefficient of X^{2^i}; reason: the paper asserts J is linearized of degree ≤ N/2 (p.38)
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 5.8, pp.39–40

import Mathlib
import Definitions.Def_GoldProxGap_quadPoly

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Lemma 5.8 (Moment equations and the coefficients of J)**, pp.39–40. Dao, Kominers, Thaler,
Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027
submission manuscript (2 November 2026, sha256 6c2d9ced…).

"Write J = Σ_{i=0}^{d−1} J_i X^{2^i}. Then J_0 = 0, and for 2 ≤ t ≤ d/2 the following are
equivalent: 1. M_1(A) = ⋯ = M_{t−1}(A) = 0; 2. J_1 = ⋯ = J_{t−1} = 0; 3. J_{d−t+1} = ⋯ = J_{d−1} = 0,
that is, deg J ≤ N/2^t. When they hold, J = Σ_{i=t}^{d−t} J_i X^{2^i} = Ĵ^{2^t},
Ĵ = Σ_{i=t}^{d−t} J_i^{2^{−t}} X^{2^{i−t}}, deg Ĵ ≤ N/2^{2t}, (5.4) where a^{2^{−r}} denotes the 2^r-th
root of a in B."

**Formalization Note.** Setting of (5.2) (p.38) with a coordinate basis `φs` of the linear
functions, `ω_i = label D (φs i)` (see `GoldProxGap.quadPoly`); `A` is an alternating binary
matrix; `J = Jpoly D φs A`, `J_i` is the coefficient of `X^{2^i}`. "Write J = Σ_{i<d} J_i X^{2^i}"
is stated as a conclusion (`J` is linearized of degree `≤ N/2`, p.38). `t ≤ d/2` is `2t ≤ d`.
`a^{2^{−t}}` is `frobRoot B 2 t a`. Degrees are in `WithBot ℕ`, so `deg J ≤ N/2^t` holds for
`J = 0`. -/
theorem lemma_5_8 {B : Type} [Field B] [Fintype B] [CharP B 2] (D : AddSubgroup B) (d : ℕ)
    (hD : Nat.card D = 2 ^ d) (φs : Fin d → (D →+ ZMod 2)) (hφs : IsCoordBasis D φs)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (hA : IsAltBin A) :
    let J := Jpoly D φs A
    let ω : Fin d → B := fun i => label D (φs i)
    J = ∑ i ∈ Finset.range d, C (J.coeff (2 ^ i)) * X ^ (2 ^ i) ∧ J.coeff 1 = 0 ∧
    ∀ t : ℕ, 2 ≤ t → 2 * t ≤ d →
      ((∀ k, 1 ≤ k → k ≤ t - 1 → goldMoment ω A k = 0) ↔
        (∀ i, 1 ≤ i → i ≤ t - 1 → J.coeff (2 ^ i) = 0)) ∧
      ((∀ k, 1 ≤ k → k ≤ t - 1 → goldMoment ω A k = 0) ↔
        (∀ i, d - t + 1 ≤ i → i ≤ d - 1 → J.coeff (2 ^ i) = 0)) ∧
      ((∀ i, d - t + 1 ≤ i → i ≤ d - 1 → J.coeff (2 ^ i) = 0) ↔
        J.degree ≤ ((2 ^ d / 2 ^ t : ℕ) : WithBot ℕ)) ∧
      ((∀ k, 1 ≤ k → k ≤ t - 1 → goldMoment ω A k = 0) →
        J = ∑ i ∈ Finset.Icc t (d - t), C (J.coeff (2 ^ i)) * X ^ (2 ^ i) ∧
        J = (∑ i ∈ Finset.Icc t (d - t), C (frobRoot B 2 t (J.coeff (2 ^ i))) * X ^ (2 ^ (i - t)))
              ^ (2 ^ t) ∧
        (∑ i ∈ Finset.Icc t (d - t), C (frobRoot B 2 t (J.coeff (2 ^ i))) * X ^ (2 ^ (i - t))).degree
          ≤ ((2 ^ d / 2 ^ (2 * t) : ℕ) : WithBot ℕ)) := by sorry

end GoldProxGap
