-- Prove2me | Theorems.Thm_HighDimStat_MatrixRank_prop10_6_nuclear_norm_oracle_inequality_v2
-- name    : HighDimStat.MatrixRank.prop10_6_nuclear_norm_oracle_inequality_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:06.887159+00:00
-- url     : https://prove2.me/theorems/82ab93d0-e7e1-4d3b-8b28-3b798d27a6cf
-- title:
--   The nuclear-norm oracle inequality for matrix regression (Proposition 10.6, goal), with corrected constants
-- statement:
--   **Proposition 10.6 (corrected constants).** The chapter's title deterministic result: a
--   direct specialization of Theorem 9.19 to the nuclear norm, giving an explicit
--   Frobenius-error oracle inequality for low-rank matrix regression.
--
--   Suppose the observation operator $\mathfrak X_n$ satisfies the restricted strong convexity
--   condition (10.17), $\frac{\|\mathfrak X_n(\Delta)\|_2^2}{2n}\ge\frac\kappa2|\!|\!|\Delta|\!|\!|_F^2-
--   c_0\frac{d_1+d_2}{n}|\!|\!|\Delta|\!|\!|_{\rm nuc}^2$ for all $\Delta$, with curvature
--   $\kappa>0$ and tolerance constant $c_0\ge0$. Then, conditioned on the good event
--   $\mathcal G(\lambda_n)=\{|\!|\!|\frac1n\sum_{i=1}^n w_iX_i|\!|\!|_2\le\lambda_n/2\}$ ($\lambda_n>0$),
--   any optimal solution $\hat\Theta$ of nuclear-norm-regularized least squares (10.16) with
--   observations $y_i=\langle\!\langle X_i,\Theta^*\rangle\!\rangle+w_i$ satisfies
--
--   $$
--   |\!|\!|\hat\Theta-\Theta^*|\!|\!|_F^2 \le 72\,\frac{\lambda_n^2}{\kappa^2}\,r +
--   \frac{1}{\kappa}\left\{16\lambda_n\sum_{j=r+1}^{d'}\sigma_j(\Theta^*) +
--   \frac{256\,c_0(d_1+d_2)}{n}\Big(\sum_{j=r+1}^{d'}\sigma_j(\Theta^*)\Big)^2\right\},
--   $$
--
--   valid for any target rank $r\in\{1,\dots,d'\}$, $d'=\min\{d_1,d_2\}$, such that
--   $256\,c_0(d_1+d_2)\,r\le\kappa n$.
--
--   **Formalization Note.** The retired version (`prop10_6_nuclear_norm_oracle_inequality`)
--   transcribed the printed bound $\frac92\frac{\lambda_n^2}{\kappa^2}r+\frac1\kappa\{2\lambda_n\,
--   \mathrm{tail}_r+\frac{32c_0(d_1+d_2)}{n}\mathrm{tail}_r^2\}$ under the printed rank condition
--   $r\le\kappa n/(128c_0(d_1+d_2))$; the accepted disproof is a fully non-degenerate instance
--   ($d_1=d_2=101$, $r=1$, $\kappa=1$, $\lambda_n=1/100$, rank condition met with equality, RSC
--   verified for every matrix, a KKT-certified global minimizer) with error $5.24>4.08$, and an
--   independent transcription of the proposition confirms the printed constants, so the **printed
--   source** is false. The proposition is Theorem 9.19 instantiated with $\Psi^2(\bar{\mathcal M})=2r$,
--   $\tau_n^2=c_0(d_1+d_2)/n$, $\Phi(\Theta^*_{\mathcal M^\perp})=\sum_{j>r}\sigma_j(\Theta^*)$; the
--   printed constants are not even those of the printed Theorem 9.19 (which would read
--   $18,\,8,\,128$), and the printed Theorem 9.19 is itself false for positive tolerance (see
--   `cor9_20_special_case_v2`). The statement formalized here is what the book's proof of Theorem
--   9.19 establishes once the tolerance term is accounted for: the cone condition gives
--   $\Phi(\Delta)^2\le32\Psi^2\|\Delta\|^2+32\Phi(\theta^*_{\mathcal M^\perp})^2$, which leaves
--   curvature $\kappa/2-32\tau_n^2\Psi^2\ge\kappa/4$ once $\tau_n^2\Psi^2\le\kappa/128$ (here
--   $256c_0(d_1+d_2)r\le\kappa n$), and then
--   $F(\Delta)\ge\frac\kappa4\|\Delta\|^2-\frac32\lambda_n\Psi\|\Delta\|-2\lambda_n\Phi(\theta^*_{\mathcal M^\perp})
--   -32\tau_n^2\Phi(\theta^*_{\mathcal M^\perp})^2$ is positive whenever
--   $\|\Delta\|^2>36\lambda_n^2\Psi^2/\kappa^2+\frac{16}{\kappa}(\lambda_n\Phi(\theta^*_{\mathcal M^\perp})
--   +16\tau_n^2\Phi(\theta^*_{\mathcal M^\perp})^2)$ (strictly, by the equality case of the AM–GM
--   step when the tail is positive and by a finer case analysis when it vanishes), which with
--   $\Psi^2=2r$ is exactly the displayed bound. The rank condition is written multiplicatively so
--   that $c_0=0$ imposes no restriction (Lean's $x/0=0$ would otherwise make the printed form
--   $r\le\kappa n/0$ unsatisfiable). Conventions as in the retired version: $c_0\ge0$,
--   $\lambda_n>0$, and all objects (`RSCNuclear`, `opNorm`, `nuclearNorm`, `tailSingularSum`,
--   `IsNuclearNormLSSolution`) are the mission's own definitions; the tail sum runs over the
--   0-indexed singular values with index $\ge r$, i.e. the book's $j=r+1,\dots,d'$ (indices beyond
--   $d'$ carry the value $0$).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 319 (PDF p. 339), Proposition 10.6, Eq. (10.18) — corrected constants (72, 16, 256 in place of the printed 9/2, 2, 32) and rank condition 256 c0 (d1+d2) r ≤ κ n (printed: 128); the printed inequality is false (accepted disproof)

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

namespace HighDimStat.MatrixRank

/-- Proposition 10.6 (p. 319), **with corrected constants and rank condition**: suppose the
observation operator `Xn` satisfies the restricted strong convexity condition (10.17) with
curvature `κ > 0` and tolerance constant `c0 ≥ 0`. Then, conditioned on the good event
`G(λn) = {|||(1/n)Σwᵢ Xᵢ|||₂ ≤ λn/2}`, any optimal solution `Θ̂` of nuclear-norm-regularized
least squares (10.16) satisfies, for any target rank `r ∈ {1,...,d'}` with
`256 c0 (d1+d2) r ≤ κ n`,
`|||Θ̂ - Θ*|||_F² ≤ 72 (λn²/κ²) r + (1/κ){16 λn Σ_{j>r} σⱼ(Θ*) + 256 c0 (d1+d2)/n (Σ_{j>r} σⱼ(Θ*))²}`.

Correction to the printed source. The printed bound
`(9/2)(λn²/κ²) r + (1/κ){2λn·tail + 32 c0(d1+d2)/n · tail²}` under the printed rank condition
`r ≤ κn/(128 c0(d1+d2))` is false: a non-degenerate instance (`d1 = d2 = 101`, `r = 1`,
`κ = 1`, `λn = 1/100`, rank condition met with equality, RSC verified for every matrix, a
KKT-certified global minimizer) has `|||Θ̂ - Θ*|||_F² = 5.24 > 4.08`. The proposition is the
instantiation of Theorem 9.19 with `Ψ²(M̄) = 2r`, `τn² = c0(d1+d2)/n`,
`Φ(Θ*_{M⊥}) = Σ_{j>r}σⱼ(Θ*)`; the printed constants are not even those of the printed
Theorem 9.19 (which would give `18, 8, 128`), and the printed Theorem 9.19 itself is false
with a positive tolerance (see `cor9_20_special_case_v2`). Running the book's proof of
Theorem 9.19 with the tolerance term accounted for — `Φ(Δ)² ≤ 32Ψ²‖Δ‖² + 32Φ(θ*_{M⊥})²` leaves
curvature `κ/2 − 32τn²Ψ² ≥ κ/4` once `τn²Ψ² ≤ κ/128` (here: `256 c0(d1+d2) r ≤ κn`), and then
`F(Δ) ≥ (κ/4)‖Δ‖² − (3/2)λnΨ‖Δ‖ − 2λnΦ(θ*_{M⊥}) − 32τn²Φ(θ*_{M⊥})² > 0` for
`‖Δ‖² > 36λn²Ψ²/κ² + (16/κ)(λnΦ(θ*_{M⊥}) + 16τn²Φ(θ*_{M⊥})²)` — gives exactly the bound
stated here. The rank condition is written multiplicatively so that `c0 = 0` (no tolerance)
imposes no restriction, as in the source. -/
theorem prop10_6_nuclear_norm_oracle_inequality_v2 {d1 d2 n : ℕ}
    (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (w : Fin n → ℝ)
    (Θstar Θhat : Matrix (Fin d1) (Fin d2) ℝ) (κ c0 lamN : ℝ) (r : ℕ)
    (hκ : 0 < κ) (hc0 : 0 ≤ c0) (hlam : 0 < lamN)
    (hRSC : RSCNuclear Xs κ c0)
    (hG : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs w) ≤ lamN / 2)
    (hsol : IsNuclearNormLSSolution Xs (fun i => traceInner (Xs i) Θstar + w i) lamN Θhat)
    (hr1 : 1 ≤ r) (hr2 : r ≤ min d1 d2)
    (hr3 : 256 * c0 * ((d1 : ℝ) + d2) * r ≤ κ * n) :
    (frobeniusNorm (Θhat - Θstar)) ^ 2 ≤
      72 * (lamN ^ 2 / κ ^ 2) * r +
        1 / κ * (16 * lamN * tailSingularSum Θstar r +
          256 * c0 * ((d1 : ℝ) + d2) / n * (tailSingularSum Θstar r) ^ 2) := by sorry

end HighDimStat.MatrixRank
