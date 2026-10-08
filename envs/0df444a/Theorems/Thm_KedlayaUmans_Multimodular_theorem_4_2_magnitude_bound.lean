-- Prove2me | Theorems.Thm_KedlayaUmans_Multimodular_theorem_4_2_magnitude_bound
-- name    : KedlayaUmans.Multimodular.theorem_4_2_magnitude_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:08.245451+00:00
-- url     : https://prove2.me/theorems/9b8ceedb-298b-450a-b3b4-9be4c565d0dd
-- title:
--   Proof of Theorem 4.2 — $0 \le \tilde f(\tilde\alpha) \le d^m(r-1)^{md} < p_1\cdots p_k$
-- statement:
--   Let $r \ge 1$, $m \ge 1$ and $d \ge 2$ be integers, let $f \in (\mathbb Z/r\mathbb Z)[X_0,\dots,X_{m-1}]$ have degree at most $d-1$ in each variable, and let $\alpha \in (\mathbb Z/r\mathbb Z)^m$. Let $\tilde f \in \mathbb Z[X_0,\dots,X_{m-1}]$ and $\tilde\alpha \in \mathbb Z^m$ be the lifts with coefficients and coordinates in $\{0,\dots,r-1\}$. Let $p_1,\dots,p_k$ be the primes at most $\ell = 16\log(d^m(r-1)^{md})$. Then
--   $$0 \;\le\; \tilde f(\tilde\alpha) \;\le\; d^m (r-1)^{md} \;<\; p_1 p_2 \cdots p_k.$$
--
--   This is the bound on which the correctness of Algorithm MULTIMODULAR rests: the integer $\tilde f(\tilde\alpha)$ lies in the range where the Chinese remainder theorem recovers it from its residues modulo $p_1,\dots,p_k$.
--
--   **Formalization Note** $\log$ is the natural logarithm. The hypotheses $d \ge 2$ and $m \ge 1$ are not written in the paper; without them the last inequality fails (for $r = 2$, $d = 1$ the bound is $1$ and there are no primes; for $m = 0$ the middle inequality fails when $r \ge 3$).
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 13, proof of Theorem 4.2

import Mathlib
import Definitions.Def_KedlayaUmans_Multimodular_Algorithm

namespace KedlayaUmans.Multimodular

/-- **Proof of Theorem 4.2** (p. 13): `0 ≤ f̃(α̃) ≤ d^m (r-1)^{md} < p₁ ⋯ p_k`, where `f̃`, `α̃` are
the lifts to `{0, …, r-1}` and `p₁, …, p_k` are the primes `≤ ℓ = 16 log(d^m (r-1)^{md})`. -/
theorem theorem_4_2_magnitude_bound {m r : ℕ} [NeZero r] (d : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m)
    (f : MvPolynomial (Fin m) (ZMod r)) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (α : Fin m → ZMod r) :
    0 ≤ MvPolynomial.eval (liftPoint α) (liftPoly f) ∧
      MvPolynomial.eval (liftPoint α) (liftPoly f) ≤ (magnitudeBound d m r : ℤ) ∧
      magnitudeBound d m r < ∏ p ∈ primesUpTo (ell d m r), p := by sorry

end KedlayaUmans.Multimodular
