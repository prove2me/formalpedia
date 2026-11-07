-- Prove2me | Theorems.Thm_GeoSemialgCSP_theorem_8_1
-- name    : GeoSemialgCSP.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:53:28.762076+00:00
-- url     : https://prove2.me/theorems/ef6749be-a61a-4bf6-87d6-37221a86f14f
-- title:
--   Theorem 8.1 — norm bound for smoothed probability vectors
-- statement:
--   Fix $d_{\mathrm{VC}}\ge1$ and $0<\eta<1$. There are constants $C\ge1$ and $b\in(0,1]$, depending only on $d_{\mathrm{VC}}$ and $\eta$, with the following property. For every $M,q\ge1$ and every $0<\kappa<1$ there is $\tau=\tau(M,q,d_{\mathrm{VC}},\eta,\kappa)>0$, independent of $R$, such that: if $G:[M]^R\to\mathcal P_q$, $F=T_{1-\eta}G$ is $\tau$-pseudorandom, $Z$ is uniform on $[M]^R$ and $\mu=\mathbb EF(Z)$, then for every $0<t\le1$ and every family $\mathcal B\subseteq2^{[q]}$ with $\mathrm{VCdim}(\mathcal B)\le d_{\mathrm{VC}}$ and $\mu(B)\le t$ for all $B\in\mathcal B$,
--   $$\mathbb E\Bigl[\max_{B\in\mathcal B}F_B(Z)\Bigr]\ \le\ C\,t^b+\kappa .\tag{16}$$
--   The same threshold $\tau$ works for all families $\mathcal B$ and all cutoffs $t$.
--
--   A smoothed pseudorandom probability vector cannot concentrate on light sets of a bounded-VC family.
--
--   Differences from the source:
--   - encoding: the alphabet [M], M ≥ 1 → any nonempty finite type W; reason: W ≅ Fin |W|; τ may depend on M, and so on W
--   - encoding: [q], coordinates 1, …, R → Fin q, Fin R; reason: index base
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 8.1, Eq. (16), p.22 (PDF p.23)

import Mathlib
import Definitions.Def_GeoSemialgCSP_NormBound

namespace GeoSemialgCSP

/-- **Theorem 8.1 (norm bound for smoothed probability vectors).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 8.1, Eq. (16),
printed p.22 (PDF p.23): for `d_VC ≥ 1` and `0 < η < 1` there are `C ≥ 1` and `b ∈ (0,1]`,
depending only on `d_VC` and `η`, with the property `NormBound d_VC η C b`: for every `M, q ≥ 1`
and `0 < κ < 1` there is `τ > 0`, independent of `R`, such that for `G : [M]^R → P_q` with
`F = T_{1−η}G` `τ`-pseudorandom, `μ = E F(Z)`, every `0 < t ≤ 1` and every family `𝓑` with
`VCdim(𝓑) ≤ d_VC` and `μ(B) ≤ t` on `𝓑`, `E[max_{B ∈ 𝓑} F_B(Z)] ≤ C t^b + κ`; the same `τ`
works for all `𝓑` and `t`. -/
theorem theorem_8_1 (dVC : ℕ) (hd : 1 ≤ dVC) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ C b : ℝ, 1 ≤ C ∧ 0 < b ∧ b ≤ 1 ∧ NormBound dVC η C b := by sorry

end GeoSemialgCSP
