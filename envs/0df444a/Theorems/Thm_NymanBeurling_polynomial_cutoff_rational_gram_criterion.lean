-- Prove2me | Theorems.Thm_NymanBeurling_polynomial_cutoff_rational_gram_criterion
-- name    : NymanBeurling.polynomial_cutoff_rational_gram_criterion
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:53:05.297425+00:00
-- url     : https://prove2.me/theorems/a45c709f-514b-47e9-abe4-c3c47b4f8981
-- title:
--   A rational Gram determinant at polynomial row cutoffs characterizes small Bagchi certificates
-- statement:
--   Take the first $D$ Bagchi atoms $(m\bmod d)/d$ with denominators $d=2,\ldots,D+1$. On the first $H$ positive integers give row $m$ weight $1/[m(m+1)]$. Let $g(D,H)$ be the determinant of the Gram matrix with the constant target appended, divided by the determinant of the Gram matrix of the atoms alone. Both matrices have rational entries.
--
--   For $H\ge D+1$ the denominator is nonzero. The gap is the least weighted squared error on those rows, and a rational minimizer attains it. Every rational certificate using those denominators, at any row cutoff, has cost at least $g(D,H)$. The attained certificate at cutoff $H$ costs at most $g+[2(D+2)^2+36(D+1)^3 g]/(H+1)$. At $H=(D+2)^4$ its cost is within $38/(D+2)$ of the gap.
--
--   Arbitrarily small finite rational certificates exist if and only if the explicit sequence $g(D,(D+2)^4)$ tends to zero. More generally any prescribed cutoff sequence $h(D)\ge(D+2)^3$ gives exactly the same zero-limit criterion. This identifies a deterministic one-parameter arithmetic condition. The convergence itself remains open.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137–146, Theorem 2. Finite-certificate frontier 5b7b7b22-9280-4b04-9e90-f2f88cb85339. The coefficient estimate starts with the finite Möbius inversion from 75892a74. The polynomial cutoffs and rational least-squares comparison are derived here.

import Definitions.Def_NymanBeurling_RationalGram

open NymanBeurling.RationalGram Filter Topology

theorem NymanBeurling.polynomial_cutoff_rational_gram_criterion :
    (∀ (c : ℕ →₀ ℚ) (N : ℕ), 1 ≤ N → (∀ k ∈ c.support, k+2 ≤ N) →
      (mass c)^2 ≤ 2*(N+1:ℚ)^2+36*(N:ℚ)^3*headEnergy c N) ∧
    (∀ (D H : ℕ), D+1 ≤ H →
      (NymanBeurling.RationalGram.gram D H).det ≠ 0 ∧ 0 ≤ gap D H ∧
      (∀ (c : ℕ →₀ ℚ), (∀ k ∈ c.support, k < D) → ∀ K, gap D H ≤ cost c K) ∧
      ∃ c : ℕ →₀ ℚ, (∀ k ∈ c.support, k < D) ∧ headEnergy c H = gap D H ∧
        cost c H ≤ gap D H+(2*(D+2:ℚ)^2+36*(D+1:ℚ)^3*gap D H)/(H+1:ℚ)) ∧
    (∀ D, ∃ c : ℕ →₀ ℚ, (∀ k ∈ c.support, k < D) ∧
      headEnergy c (rows D) = gap D (rows D) ∧
      cost c (rows D) ≤ gap D (rows D)+38/(D+2:ℚ)) ∧
    (SmallCertificates ↔ Tendsto (fun D => gap D (rows D)) atTop (𝓝 0)) ∧
    (∀ h : ℕ → ℕ, (∀ D, (D+2)^3 ≤ h D) →
      (SmallCertificates ↔ Tendsto (fun D => gap D (h D)) atTop (𝓝 0))) := by sorry
