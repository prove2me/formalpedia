-- Prove2me | Theorems.Thm_HypercliqueRefutation_FourClique_Supplement_lemma_3_1
-- name    : HypercliqueRefutation.FourClique.Supplement.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:27:38.925294+00:00
-- url     : https://prove2.me/theorems/0d0bfb3c-9e2b-47c5-8587-efdd7070b6ab
-- title:
--   Lemma 3.1 (Main identity) — full polynomial Walsh identity
-- statement:
--   Let $n\ge0$, let $K$ be any characteristic-zero field, and let $X,Y,Z,W:(\mathbb F_2^n)^3\to K$ be four independent arrays. With the full polynomial $\Phi$ of Eq.(4), the unnormalized transforms $U,V$ and the zero-zero coordinate count $\ell$ defined above, equality holds as polynomials:
--
--   $$
--   \Phi(z)=\frac1{2^n}\sum_{a,b,e,\xi\in\mathbb F_2^n}
--   (2z-1)^{\ell(e,\xi)}U_{a,b,e}(\xi)V_{a,b,e}(\xi).
--   $$
--
--   Every coefficient is retained. In particular, this is not restricted to the evaluation at $z=1$, to one coefficient, or to Boolean arrays. The scalar denominator is nonzero in characteristic zero, including $n=0$, when the cube has one element. This identity supplies the spectral polynomial representation used by Theorem 3.2.
--
--   Differences from the source:
--   - reading: binary index group and unspecified scalar arrays, with a conflicting binary codomain in the p.9 footnote → binary indices but arbitrary characteristic-zero coefficient field; reason: integer polynomial coefficients, Fourier signs and the factor 2^(-n) in Eqs.(4)–(5) require the characteristic-zero scalar reading
--   - encoding: bitwise xor, parity dot product and n minus union-support cardinality → pointwise addition in ZMod 2, the same sign via the integer dot-product exponent, and a count of zero-zero coordinates; reason: these are identical finite binary operations, including the empty cube; equality is in K[z] with U,V embedded as constants
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026); Lemma 3.1 and Eq.(5), printed/PDF p.8; Φ in Eq.(4), p.7; proof §3.2, pp.9-10.

import Definitions.Def_HypercliqueRefutation_FourClique_Supplement_CubePolynomial

set_option autoImplicit false

namespace HypercliqueRefutation.FourClique.Supplement

/-- Chan--Itakura--Ma--Yu, STOC 2027 submission #1431 (October 2026),
    Lemma 3.1, Eq.(5), p.8; Eq.(4), p.7; proof pp.9--10.
    Polynomial equality over every characteristic-zero field, including n = 0. -/
theorem lemma_3_1 {K : Type*} [Field K] [CharZero K] (n : ℕ)
    (X Y Z W : CubeArray K n) : phi X Y Z W = spectralPhi X Y Z W := by sorry

end HypercliqueRefutation.FourClique.Supplement
