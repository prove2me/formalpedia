-- Prove2me | Theorems.Thm_KWSpectrum_Estimator_legendre
-- name    : KWSpectrum.Estimator.legendre
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:16.917982+00:00
-- url     : https://prove2.me/theorems/ca30fdb6-6092-485c-a7fa-c575c6e7dced
-- title:
--   p. 4 — the rate function is the Legendre transform $I(s) = \sup_\eta(\eta\cdot s - \ln\sum_\alpha r_\alpha e^{\eta_\alpha})$
-- statement:
--   Let $r, s \in \Sigma$ and let $I(s) = \sum_j s_j(\ln s_j - \ln r_j) \in [0,\infty]$ be the rate function (13), with $0\ln 0 = 0$ and $I(s) = +\infty$ when $s_j > 0 = r_j$ for some $j$. Then
--   $$I(s) = \sup_{\eta\in\mathbb R^d}\Big(\eta\cdot s - \ln\sum_\alpha r_\alpha e^{\eta_\alpha}\Big),$$
--   the supremum being taken in $(-\infty, +\infty]$ over all $\eta \in \mathbb R^d$.
--
--   This identifies the rate function produced by the Gärtner–Ellis theorem from $c(\eta)$ in (25) with the relative entropy of $s$ with respect to $r$.
--
--   **Formalization Note** The supremum is an `EReal` supremum; $\sum_\alpha r_\alpha e^{\eta_\alpha} > 0$ for $r \in \Sigma$, so the real logarithm is the true one.
--
--   Differences from the source: none.
-- source:
--   Keyl & Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1, p. 4 (sentence after eq. (25)), with eq. (13), p. 3

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, p. 4: the rate function (13) is the Legendre
transform of `c(η) = ln Σ_α r_α e^{η_α}`: `I(s) = sup_{η ∈ ℝ^d} (η · s − c(η))` for `r, s ∈ Σ`,
in `[0, ∞]`. -/
theorem legendre {d : ℕ} (r s : Fin d → ℝ) (hr : r ∈ SpectrumSet d) (hs : s ∈ SpectrumSet d) :
    rate r s = ⨆ η : Fin d → ℝ,
      (((∑ j : Fin d, η j * s j) - Real.log (∑ α : Fin d, r α * Real.exp (η α)) : ℝ) : EReal) := by sorry

end KWSpectrum.Estimator
