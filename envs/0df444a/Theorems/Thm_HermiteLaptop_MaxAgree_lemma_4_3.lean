-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_lemma_4_3
-- name    : HermiteLaptop.MaxAgree.lemma_4_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T18:14:58.045241+00:00
-- url     : https://prove2.me/theorems/a563790b-2f89-41ac-ab16-6ff38a744230
-- title:
--   Lemma 4.3 — nonnegative Bernstein coefficients on [u, v] certify q ≥ 0 on [u, v]
-- statement:
--   Let $q$ be a real polynomial of degree at most $d$, written in the Bernstein basis of degree $d$ on an interval $[u,v]$ as
--   $$q(\rho)=\sum_{i=0}^d\beta_i\binom di\Big(\frac{\rho-u}{v-u}\Big)^i\Big(\frac{v-\rho}{v-u}\Big)^{d-i}.$$
--   If $\beta_i\ge0$ for all $i$, then $q\ge0$ on $[u,v]$. This is the exact-arithmetic certificate used to verify (25) on infinitely many $\rho$.
--
--   **Formalization Note.** The representation is a pointwise identity for all real $\rho$; $u<v$.
--
--   Differences from the source:
--   - encoding: an interval [u, v] → u < v; reason: the printed basis divides by v − u; the hypothesis excludes only the undefined degenerate case
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 28 (PDF 31), Lemma 4.3

import Mathlib

namespace HermiteLaptop.MaxAgree

/-- Lemma 4.3 (Bernstein certificate): if `q` has degree at most `d` and
`q(ρ) = Σ_{i=0}^{d} β_i binom(d,i) ((ρ−u)/(v−u))ⁱ ((v−ρ)/(v−u))^{d−i}` with all `β_i ≥ 0`, then
`q ≥ 0` on `[u, v]`. -/
theorem lemma_4_3 (q : Polynomial ℝ) (d : ℕ) (hdeg : q.natDegree ≤ d) (u v : ℝ) (huv : u < v)
    (β : ℕ → ℝ)
    (hrep : ∀ ρ : ℝ, q.eval ρ = ∑ i ∈ Finset.range (d + 1),
      β i * (d.choose i : ℝ) * ((ρ - u) / (v - u)) ^ i * ((v - ρ) / (v - u)) ^ (d - i))
    (hβ : ∀ i ≤ d, 0 ≤ β i) :
    ∀ ρ ∈ Set.Icc u v, 0 ≤ q.eval ρ := by sorry

end HermiteLaptop.MaxAgree
