-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_eq_6
-- name    : OptInapprox.MaxCut.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:27.252014+00:00
-- url     : https://prove2.me/theorems/355f5436-e010-4669-bc40-35e41ed07306
-- title:
--   (6), §8.3, p. 19 — Pr[acc] = 1/2 − (1/2)·E_v[𝕊_ρ(g_v)]
-- statement:
--   Let $\mathcal L$ be a Unique Label Cover instance regular on the $V$ side, let $-1<\rho<0$, and let $f_w:\{-1,1\}^M\to\{-1,1\}$ ($w\in W$) be any proof. With the polling functions $g_v(z)=\mathbf E_{w\sim v}[f_w(z\circ\sigma_{v,w})]$, the acceptance probability of the verifier of §8.1 is
--   $$\Pr[\mathrm{acc}]=\frac12-\frac12\,\mathbf E_{v}\big[\mathbb S_\rho(g_v)\big],$$
--   with $v$ uniform in $V$ and $\mathbb S_\rho$ the noise stability.
--
--   This arithmetization turns the acceptance probability of the test into an average of noise stabilities, to which Majority Is Stablest applies.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 19, §8.3 Soundness, eq. (6)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Verifier

namespace OptInapprox.MaxCut

theorem eq_6 (L : ULC) (hreg : L.IsVRegular) (ρ : ℝ) (hρ₁ : -1 < ρ) (hρ₂ : ρ < 0)
    (F : Fin L.nW → (Fin L.M → Bool) → Bool) :
    accProb L ρ F = 1 / 2 - 1 / 2 * ((L.nV : ℝ)⁻¹ * ∑ v, noiseStab ρ (gv L F v)) := by sorry

end OptInapprox.MaxCut
