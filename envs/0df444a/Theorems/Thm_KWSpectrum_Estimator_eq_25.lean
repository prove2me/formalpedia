-- Prove2me | Theorems.Thm_KWSpectrum_Estimator_eq_25
-- name    : KWSpectrum.Estimator.eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:19.21825+00:00
-- url     : https://prove2.me/theorems/7a8c2a25-99cd-494c-aeda-ad932b30a197
-- title:
--   Eqs. (22)–(25) — the scaled cumulant generating function $c(\eta) = \ln\sum_\alpha r_\alpha e^{\eta_\alpha}$ on the ordered cone
-- statement:
--   Let $\rho$ be a $d\times d$ density matrix with spectrum $r \in \Sigma$ (eigenvalues in decreasing order), and let $\eta \in \mathbb R^d$ with $\eta_1 \ge \eta_2 \ge \dots \ge \eta_d$. Then
--   $$\frac1N \ln \int_\Sigma K_N(ds)\, e^{N\eta\cdot s} = \frac1N \ln \sum_Y \operatorname{tr}\big(\rho^{\otimes N}P_Y\big)\, e^{\eta\cdot Y} \;\xrightarrow[N\to\infty]{}\; c(\eta) = \ln \sum_\alpha r_\alpha e^{\eta_\alpha},$$
--   where $Y$ runs over the Young frames with $N$ boxes and at most $d$ rows and $\eta\cdot Y = \sum_i \eta_i Y_i$.
--
--   This is the limit (14) computed from group-theoretical data; by the Gärtner–Ellis theorem it determines the rate function as its Legendre transform.
--
--   **Formalization Note** The sum inside the logarithm is strictly positive for $N \ge 1$ (the one-row frame contributes at least $(r_1 e^{\eta_1})^N > 0$), so the real logarithm is the true one.
--
--   Differences from the source:
--   - generalization: $r_\alpha = e^{h_\alpha}$ eigenvalues of a non-singular density operator, $h, \eta \rhd 0$ (strictly decreasing) → every density matrix $\rho$ (singular allowed) and every weakly decreasing $\eta$; reason: the limit holds there; the paper's case is included.
-- source:
--   Keyl & Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1, p. 4, eqs. (22)–(25) (with eq. (14), p. 3)

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur Filter Topology

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, p. 4, eqs. (22)–(25): for a density matrix `ρ` with
decreasingly ordered spectrum `r` and every decreasingly ordered `η ∈ ℝ^d`,
`(1/N) ln ∫_Σ K_N(ds) e^{Nη·s} = (1/N) ln Σ_Y tr(ρ^{⊗N} P_Y) e^{η·Y} → c(η) = ln Σ_α r_α e^{η_α}`. -/
theorem eq_25 {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ)
    (r : Fin d → ℝ) (hr : IsSpectrumOf ρ r) (η : Fin d → ℝ) (hη : Antitone η) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∑ Y : Partition d N,
        frameProb ρ Y * Real.exp (∑ i : Fin d, η i * (Y.val.rowLen i.val : ℝ))))
      atTop (𝓝 (Real.log (∑ α : Fin d, r α * Real.exp (η α)))) := by sorry

end KWSpectrum.Estimator
