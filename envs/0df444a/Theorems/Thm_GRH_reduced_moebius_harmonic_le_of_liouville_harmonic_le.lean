-- Prove2me | Theorems.Thm_GRH_reduced_moebius_harmonic_le_of_liouville_harmonic_le
-- name    : GRH.reduced_moebius_harmonic_le_of_liouville_harmonic_le
-- status  : Proved
-- author  : @pragyan
-- created : 2026-11-21T01:52:32.267571+00:00
-- url     : https://prove2.me/theorems/ae1711f2-ddbb-45fb-a092-1331f4b25896
-- title:
--   Square-divisor transfer from reduced harmonic Liouville to reduced harmonic Möbius sums
-- statement:
--   Let $q\ge1$, $1/2<\sigma\le1$, and $C\ge0$. Write $H_{f,q}(U)=\sum_{1\le n\le U,(n,q)=1} f(n)/n$. If
--   $$|H_{\lambda,q}(U)|\le C(U+1)^{\sigma-1}\quad\text{for every }U\ge0,$$
--   then for every $U\ge0$,
--   $$|H_{\mu,q}(U)|\le C\zeta(2\sigma)(U+1)^{\sigma-1}.$$
--   This conditional estimate transfers the principal harmonic cancellation between the two arithmetic functions without loss of exponent. The zeta factor is finite because $2\sigma>1$; the Lean statement writes it as the convergent sum over positive integers, with the zero index contributing zero.
-- source:
--   Square-divisor inversion μ(n)=∑_{d²|n} μ(d)λ(n/d²), adapted in the coprime harmonic normalization. The coefficient identity is verified in the accepted proof of https://prove2.me/theorems/ed342a94-f581-487e-a655-dd5a9b0ff82e. The harmonic summation and floor-power estimates follow the accepted proof of https://prove2.me/theorems/ca0f885d-0502-476c-a262-63b801881ece. Arithmetic functions as in DLMF §27.2, https://dlmf.nist.gov/27.2.

import Definitions.Def_GRH_MoebiusBilinear
open GRH
open scoped BigOperators

theorem GRH.reduced_moebius_harmonic_le_of_liouville_harmonic_le
    (q : ℕ) [NeZero q] (σ C : ℝ) (hhalf : 1/2 < σ) (hone : σ ≤ 1) (hC : 0 ≤ C)
    (H : ∀ U : ℕ, |reducedLiouvilleHarmonic q U| ≤ C * ((U : ℝ)+1)^(σ-1))
    (U : ℕ) :
    |reducedMoebiusHarmonic q U| ≤
      (C * ∑' d : ℕ, ((d : ℝ)^(2*σ))⁻¹) * ((U : ℝ)+1)^(σ-1) := by sorry
