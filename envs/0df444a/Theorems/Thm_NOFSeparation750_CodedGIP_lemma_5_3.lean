-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_lemma_5_3
-- name    : NOFSeparation750.CodedGIP.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:43:24.45121+00:00
-- url     : https://prove2.me/theorems/1d00b83e-a91d-413c-8c1f-6cc2275341b1
-- title:
--   Lemma 5.3 — exact generalized-inner-product cylinder correlation bound
-- statement:
--   Fix integers $k\ge2$, $w\ge1$ and any finite field of cardinality $q=2^a$ with $a\ge1$. Let $\nu$ be uniform on $(\mathbb F_q^w)^k$. For every cylinder intersection $B$ and every $\tau\in\mathbb F_q$,
--   $$\left|\nu\bigl(B\cap\{y:\operatorname{GIP}_{q,w}^{k}(y)=\tau\}\bigr)-\frac{\nu(B)}{q}\right|\le\left(1-\frac1q\right)\left(1-\left(1-\frac1q\right)^{k-1}\right)^{w/2^{k-1}}.$$
--   The final exponent is the real quotient $w/2^{k-1}$. The prefactor $1-1/q$ and the domain of every power-of-two field are retained. This is the precise correlation estimate used to control accepting cylinders.
--
--   Differences from the source:
--   - encoding: q a power of two and uniform probabilities → q=2^a with a≥1, any field with that cardinality, and exact cardinality ratios; reason: these are the same finite fields and uniform laws; q=1 is not a field
--   - encoding: the exponent w/2^(k−1) → Real.rpow with a real quotient and natural exponent k−1 in the denominator; reason: this preserves the fractional exponent; k≥2 ensures that subtraction is not truncated
--   - encoding: indices [r] and Boolean values {0,1} → zero-based Fin indices and Bool; reason: order-preserving relabeling changes no inputs, cylinders, or communication costs
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), Lemma 5.3, p.9, citing [BDPW10, Fact 4.11]; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Cylinders

namespace NOFSeparation750.CodedGIP

/-- Lemma 5.3, p.9. The final exponent is real w/2^(k-1), and the prefactor is
retained. Every finite field of power-of-two cardinality is included. -/
theorem lemma_5_3 (k w a : ℕ) (hk : 2 ≤ k) (hw : 1 ≤ w) (ha : 1 ≤ a)
    (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ a)
    (B : Set (Fin k → Fin w → F)) (hB : IsCylinderIntersection B) (τ : F) :
    |uniformMass (B ∩ {y | gip y = τ}) - uniformMass B / (Fintype.card F : ℝ)| ≤
      (1 - 1 / (Fintype.card F : ℝ)) *
        Real.rpow (1 - (1 - 1 / (Fintype.card F : ℝ)) ^ (k - 1))
          ((w : ℝ) / (2 : ℝ) ^ (k - 1)) := by sorry

end NOFSeparation750.CodedGIP
