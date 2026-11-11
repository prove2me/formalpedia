-- Prove2me | Theorems.Thm_LogLogJam_lemma_4_8
-- name    : LogLogJam.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:42.660254+00:00
-- url     : https://prove2.me/theorems/b725aa83-bd8e-4bf7-aae4-0d0e10c9da25
-- title:
--   Lemma 4.8 — $V_\theta^{\oplus k}$ corresponds to $\rho e^{2i\theta}I_k\in\mathfrak D_k$
-- statement:
--   Let $\lambda\ge1$, $\rho=(\lambda-1)/(\lambda+1)$, $\theta\in\mathbb R$ and $k\ge0$. Then $K=\rho e^{2i\theta}I_k$ lies in the Siegel disk $\mathfrak D_k$ and
--
--   $$
--   V_{\rho e^{2i\theta}I_k}=V_{\lambda,\theta}\otimes I_k=V_\theta^{\oplus k}.
--   $$
--
--   The $k$ copies of the squeezed vacuum are the Siegel-disk point $\rho e^{2i\theta}I_k$; this is how the proof of Lemma 6.1 computes $\det(V_\theta^{\oplus k}+W)$.
--
--   Differences from the source:
--
--   - generalization: the squeezed family with $\lambda>1$ (§5.1) → every $\lambda\ge1$ and every $k\ge0$; reason: $\lambda=1$ is the vacuum ($\rho=0$) and $k=0$ is the empty case; the statement specializes to the source's
--   - encoding: “the corresponding point in $\mathfrak D_k$” → $K\in\mathfrak D_k$ and $V_K=V_\theta^{\oplus k}$ with $V_K$ the formula of Lemma 4.6; reason: the correspondence of §4.4 is through the covariance matrix of $|\psi_K\rangle$, which Lemma 4.6 computes
--   - encoding: $V_\theta^{\oplus k}$ and $2k\times2k$ matrices on $k$ modes → index $\mathrm{Fin}\,2\times\mathrm{Fin}\,k$ in the q-then-p order, $V_\theta^{\oplus k}=V_\theta\otimes I_k$ (Kronecker, $2\times2$ block outside), $\Omega_k=[[0,I_k],[-I_k,0]]$; reason: the order the page itself uses for $V_\theta^{\oplus k}$ in Lemma 4.8, Lemma 4.6 and the proof of Lemma 6.1 (§4.2, p.17: the q-then-p reordering gives $V\otimes I_k$); a permutation of coordinates, same instances
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Lemma 4.8, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_LogLogJam_VK

open Matrix

namespace LogLogJam

/-- **Lemma 4.8** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 4.8, p.21): "For k-mode pure Gaussian covariance matrix V_θ^{⊕k}, the
corresponding point in D_k is ρe^{2iθ}I_k, where ρ = (λ−1)/(λ+1)."

Stated as: `ρe^{2iθ}I_k ∈ D_k` and `V_{ρe^{2iθ}I_k} = V_{λ,θ} ⊗ I_k`, for every `λ ≥ 1` (`λ = 1` is the
vacuum, `ρ = 0`), every `θ` and every `k`. -/
theorem lemma_4_8 (lam θ : ℝ) (hlam : 1 ≤ lam) (k : ℕ) :
    InSiegelDisk ((((lam - 1) / (lam + 1) : ℝ) * Complex.exp (2 * θ * Complex.I)) •
        (1 : Matrix (Fin k) (Fin k) ℂ)) ∧
      VK ((((lam - 1) / (lam + 1) : ℝ) * Complex.exp (2 * θ * Complex.I)) •
        (1 : Matrix (Fin k) (Fin k) ℂ)) = VsqK lam θ k := by sorry

end LogLogJam
