-- Prove2me | Theorems.Thm_OWFLocalDesc_lemma_4_8
-- name    : OWFLocalDesc.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:47:41.007807+00:00
-- url     : https://prove2.me/theorems/680184a3-6332-4411-82d2-93bd970c2576
-- title:
--   Lemma 4.8 (PAC approximation to uniform data)
-- statement:
--   Fix a polynomial sample-size schedule $m(n)\ge1$. There is a fixed PAC-style sampler $D_{\mathrm{ind}}$ with uniform points such that for every $n\ge1$
--   $$\mathrm{TV}(D_{\mathrm{ind},n},D_{0,n})=\mathbb E_X\big[1-2^{N_{\mathrm{dist}}(X)-m(n)}\big]\ \le\ \binom{m(n)}{2}2^{-n},$$
--   where $X$ is uniform on $(\{0,1\}^n)^{m(n)}$ and $N_{\mathrm{dist}}(X)$ is the number of distinct points in $X$.
--
--   This sampler transfers the easiness of Theorem 5.1 from PAC-style samples to uniform data (Corollary 5.3), since collisions between uniform points are rare.
--
--   Differences from the source:
--   - encoding: a polynomial sample-size schedule m(n) (with the standing m ≥ 1) → a `QuantumPRC.EffPoly` schedule with m n ≥ 1; reason: EffPoly is polynomially bounded and polynomial-time computable; every positive real polynomial is dominated by an ℕ[X] polynomial and the bounds are monotone in p
--   - encoding: a concept sampler Q(1^n; r) outputting a program c_r evaluated within τ_Q(n) steps → a polynomial-time evaluator (1^n, r, z) ↦ c_r(z) (`PACSampler.conc`); reason: producing c_r in polynomial time and evaluating it in polynomial time is the same as a polynomial-time evaluator
--   - encoding: N_dist(X), the number of distinct points; E_X → the size of the image of X; the average over ({0,1}^n)^{m(n)}; reason: the same quantity
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Lemma 4.8, p.23

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_HasUniformPoints
import Definitions.Def_OWFLocalDesc_tvUniform
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Lemma 4.8 (PAC approximation to uniform data).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Lemma 4.8,
p.23: "Fix a polynomial sample-size schedule m(n). There is a fixed PAC-style sampler D_ind with
uniform points such that TV(D_{ind,n}, D_{0,n}) = E_X[1 − 2^{N_dist(X)−m(n)}] ≤ (m(n) choose 2) 2^{−n},
where N_dist(X) is the number of distinct points in X."

**Formalization Note.** `X` is uniform on `({0,1}ⁿ)^{m(n)}`; `N_dist(X)` is the size of the image
of `X`. Both the identity and the bound hold at every positive point length. `m` is a
`QuantumPRC.EffPoly` schedule with the standing `m ≥ 1`. -/
theorem lemma_4_8 (m : ℕ → ℕ) (hm : QuantumPRC.EffPoly m) (hm1 : ∀ n, 1 ≤ m n) :
    ∃ D : PACSampler, HasUniformPoints D ∧
      ∀ n : ℕ, 0 < n →
        tvUniform D (m n) n =
            (∑ X : Fin (m n) → Fin n → Bool,
                (1 - (2 : ℝ) ^ (((Finset.univ.image X).card : ℤ) - (m n : ℤ)))) /
              (2 : ℝ) ^ (m n * n) ∧
          tvUniform D (m n) n ≤ ((m n).choose 2 : ℝ) / (2 : ℝ) ^ n := by sorry

end OWFLocalDesc
