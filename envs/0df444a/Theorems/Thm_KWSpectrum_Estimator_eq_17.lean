-- Prove2me | Theorems.Thm_KWSpectrum_Estimator_eq_17
-- name    : KWSpectrum.Estimator.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:39.901591+00:00
-- url     : https://prove2.me/theorems/657568ce-1991-4ab5-a883-85675b76e3b4
-- title:
--   Eqs. (17)–(18) — $\operatorname{tr}(\rho^{\otimes N}P_Y) = \chi_Y(\rho)\dim\mathcal S_Y$ for every $d\times d$ matrix $\rho$
-- statement:
--   Let $Y$ be a Young frame with $N$ boxes and at most $d$ rows, $\mathcal R_Y \subseteq (\mathbb C^d)^{\otimes N}$ the Schur module of shape $Y$ (the image of the Young symmetrizer acting on tensor space), $\pi_Y(\rho)$ the action of $\rho^{\otimes N}$ on $\mathcal R_Y$, and $\mathcal S_Y$ the Specht module of $S_N$ of shape $Y$. For every complex $d\times d$ matrix $\rho$,
--   $$\operatorname{tr}\big(\rho^{\otimes N}P_Y\big) = \chi_Y(\rho)\,\dim\mathcal S_Y, \qquad \chi_Y(\rho) := \operatorname{tr}\pi_Y(\rho).$$
--
--   This converts the frame probabilities into characters of the irreducible representations $\pi_Y$ of $GL(d,\mathbb C)$, which is the entry point of the representation-theoretic estimates of the proof.
--
--   **Formalization Note** $\pi_Y(\rho)$ is the published `polynomialRepresentation Y ρ`, the tensor-power action compressed to the Schur module (which it leaves invariant), defined for singular $\rho$ by the same formula. $\dim\mathcal S_Y$ is the dimension of the published `spechtSpace Y`.
--
--   Differences from the source:
--   - generalization: $\rho$ non-singular ("for simplicity we assume that ρ is non-singular") → every complex $d\times d$ matrix $\rho$; reason: both sides are given by the same polynomial formula in the entries of $\rho$; the non-singular case is included.
-- source:
--   Keyl & Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1, p. 3, eqs. (17)–(18)

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, p. 3, eqs. (17)–(18):
`tr(ρ^{⊗N} P_Y) = χ_Y(ρ) dim(S_Y)`, where `χ_Y(ρ) = tr π_Y(ρ)` is the trace of the action of `ρ`
on the Schur module `R_Y` and `S_Y` is the Specht module; for every `d × d` matrix `ρ`. -/
theorem eq_17 {d N : ℕ} (Y : Partition d N) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (piKron N ρ * isotypicProjector Y).trace =
      LinearMap.trace ℂ (schurModule Y) (polynomialRepresentation Y ρ) *
        (Module.finrank ℂ (spechtSpace Y) : ℂ) := by sorry

end KWSpectrum.Estimator
