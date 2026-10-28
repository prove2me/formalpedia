-- Prove2me | Theorems.Thm_KWSpectrum_Estimator_main_theorem
-- name    : KWSpectrum.Estimator.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:16.330273+00:00
-- url     : https://prove2.me/theorems/d631d197-7447-41f5-9f8f-315c1f8fe016
-- title:
--   Theorem (§II) (corrected: sign of (12); (12) for non-singular ρ; closed Σ) — Y/N is asymptotically exact, with large-deviation rate the relative entropy
-- statement:
--   Let $d \ge 1$, let $\rho$ be a density matrix on $\mathbb C^d$, and let $r \in \Sigma$ be its spectrum, its eigenvalues in decreasing order. Measure $\rho^{\otimes N}$ with the projections $P_Y$ onto the summands $\mathcal R_Y\otimes\mathcal S_Y$ of the Schur–Weyl decomposition of $(\mathbb C^d)^{\otimes N}$, and report $Y/N$. Let $K_N(\Delta) = \operatorname{tr}(E_N(\Delta)\rho^{\otimes N})$ with $E_N(\Delta) = \sum_{Y:\,Y/N\in\Delta}P_Y$ be the law of the outcome, and $I(s) = \sum_j s_j(\ln s_j - \ln r_j) \in [0,\infty]$ the rate function. Then:
--
--   1. **Asymptotic exactness (10).** For every function $f$ continuous on $\Sigma$,
--   $$\lim_{N\to\infty}\sum_Y f\Big(\frac YN\Big)\operatorname{tr}\big(\rho^{\otimes N}P_Y\big) = f(r).$$
--   2. **Error estimate (12), corrected.** If $\rho$ is non-singular, then for every $\Delta \subseteq \Sigma$ with small boundary (its interior relative to $\Sigma$ is dense in its closure relative to $\Sigma$),
--   $$\lim_{N\to\infty}\frac1N\ln K_N(\Delta) = -\inf_{s\in\Delta} I(s).$$
--   3. **Large-deviation bounds.** For every $\rho$ and every $\Delta\subseteq\Sigma$, with interior and closure relative to $\Sigma$,
--   $$-\inf_{s\in\operatorname{int}\Delta} I(s) \le \liminf_{N\to\infty}\frac1N\ln K_N(\Delta) \le \limsup_{N\to\infty}\frac1N\ln K_N(\Delta) \le -\inf_{s\in\operatorname{cl}\Delta} I(s).$$
--
--   The theorem says that measuring the Young frame and normalizing it is a consistent estimator of the spectrum of $\rho$, and that its error probabilities decay exponentially in the number of copies, at a rate given by the classical relative entropy of the estimate with respect to the true spectrum.
--
--   **Formalization Note** Logarithms are taken in the extended reals with $\ln 0 = -\infty$, so an impossible event has rate $-\infty$; limits, $\liminf$, $\limsup$ and infima are in `EReal` (the infimum over the empty set is $+\infty$). Non-singularity is $\det\rho\ne0$, equivalently $r_d > 0$. The hypothesis that $\rho$ is a density matrix is also implied by $r$ being its spectrum; both are stated.
--
--   Differences from the source:
--   - correction: (12) $\lim\frac1N\ln K_N(\Delta) = \inf_\Delta I$ → $\lim\frac1N\ln K_N(\Delta) = -\inf_\Delta I$; reason: the left side is $\le 0$ and the right side can be positive: for $d = 2$, $r = (0.7, 0.3)$, $\Delta = \{s\in\Sigma : s_1 \ge 0.9\}$ (small boundary) $\inf_\Delta I = 0.9\ln(9/7) + 0.1\ln(1/3) \approx 0.116 > 0$; the paper's own (11) has the minus sign.
--   - correction: $\Sigma = \{s \mid s_1 > s_2 > \dots > s_d,\ \sum_j s_j = 1\}$ (strict, (5)–(6)) → the closed ordered simplex $s_1 \ge \dots \ge s_d \ge 0$, $\sum_j s_j = 1$; reason: with the strict order $Y/N$ for $Y = (N,0,\dots,0)$ is not in $\Sigma$, so (9) is ill-typed; p. 1 writes $r_1 \ge \dots \ge r_d \ge 0$ and Fig. 1 has the corners $(1/2,1/2,0)$ and $(1/3,1/3,1/3)$ in $\Sigma$.
--   - correction: (12) for every $\rho$ → (12) for non-singular $\rho$; reason: for $d = 3$, $\rho = \operatorname{diag}(1/2,1/2,0)$, $p = (3/4,1/4,0)$, $B = \{s\in\Sigma : |s-p| < 0.01,\ s_3 > 0\}$, $\Delta = B\cup\{p\}$ has small boundary, but $K_N(\Delta) = \operatorname{tr}(\rho^{\otimes N}P_{Np}) > 0$ iff $4 \mid N$, so $\frac1N\ln K_N(\Delta)$ alternates between $-\infty$ and about $-I(p)$ and has no limit; the paper's "for every $\rho$" is kept by the bounds of item 3.
--   - generalization: "for any set $\Delta\subset\Sigma$ with small boundary" → item 3, the lower bound with the relative interior and the upper bound with the relative closure, for every $\rho$ and every $\Delta\subseteq\Sigma$; reason: for non-singular $\rho$ and small-boundary $\Delta$ the two bounds coincide with $-\inf_\Delta I$ since $I$ is continuous on $\Sigma$, giving item 2.
--   - generalization: measurable $\Delta\subset\Sigma$ → every subset $\Delta\subseteq\Sigma$; reason: $K_N$ is a finite sum over frames, defined for every subset; measurable sets are included.
--   - encoding: $\frac1N\ln K_N(\Delta)$ real → in the extended reals with $\ln 0 = -\infty$, $I$ valued in $[0,+\infty]$; reason: $K_N(\Delta)$ can be $0$ and $I$ can be $+\infty$; same values wherever the source's expressions are finite.
--   - encoding: "the spectrum $r$ of $\rho$" → $r\in\Sigma$ and $\rho = U\operatorname{diag}(r)U^*$ for a unitary $U$; reason: by the spectral theorem every density matrix has exactly one such $r$.
--   - encoding: rows and coordinates $1,\dots,d$ → `Fin d` with index $0$; reason: Lean convention, same instances.
-- source:
--   Keyl & Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1, p. 3, Theorem (§II), eqs. (12)–(13), with p. 2, eqs. (5)–(10) (asymptotic exactness) and p. 3 (small boundary)

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur Filter Topology

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, Theorem (§II), p. 3, with eq. (10), p. 2
(corrected: sign of (12); (12) for non-singular ρ; Σ closed).
For a `d`-level density matrix `ρ` with decreasingly ordered spectrum `r ∈ Σ`:
(a) the laws `K_N` of `Y/N` converge weakly to the point mass at `r`;
(b) if `ρ` is non-singular, `lim (1/N) ln K_N(Δ) = −inf_{s∈Δ} I(s)` for every `Δ ⊆ Σ` with small
boundary (relative to `Σ`);
(c) for every `ρ` and every `Δ ⊆ Σ`, the large-deviation bounds
`−inf_{int Δ} I ≤ liminf (1/N) ln K_N(Δ) ≤ limsup (1/N) ln K_N(Δ) ≤ −inf_{cl Δ} I`. -/
theorem main_theorem {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ)
    (r : Fin d → ℝ) (hr : IsSpectrumOf ρ r) :
    (∀ f : (Fin d → ℝ) → ℝ, ContinuousOn f (SpectrumSet d) →
      Tendsto (fun N : ℕ => ∑ Y : Partition d N, f (youngFrac Y) * frameProb ρ Y)
        atTop (𝓝 (f r))) ∧
    (ρ.det ≠ 0 → ∀ Δ : Set (Fin d → ℝ), Δ ⊆ SpectrumSet d → HasSmallBoundary Δ →
      Tendsto (logRate ρ Δ) atTop (𝓝 (-(⨅ s ∈ Δ, rate r s)))) ∧
    (∀ Δ : Set (Fin d → ℝ), Δ ⊆ SpectrumSet d →
      -(⨅ s ∈ relInterior Δ, rate r s) ≤ liminf (logRate ρ Δ) atTop ∧
      limsup (logRate ρ Δ) atTop ≤ -(⨅ s ∈ relClosure Δ, rate r s)) := by sorry

end KWSpectrum.Estimator
