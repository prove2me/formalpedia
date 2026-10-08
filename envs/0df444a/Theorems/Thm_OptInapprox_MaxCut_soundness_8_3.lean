-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_soundness_8_3
-- name    : OptInapprox.MaxCut.soundness_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:28:22.097784+00:00
-- url     : https://prove2.me/theorems/dfb3f69a-9c63-4e93-bb7f-9a745ab9e0ec
-- title:
--   §8.3 Soundness, pp. 19–20 — Pr[acc] ≥ (arccos ρ)/π + ε forces OPT ≥ γ′(ε, ρ), independent of M
-- statement:
--   Assume the Majority Is Stablest theorem. Fix $-1<\rho<0$ and $\epsilon>0$. Then there is $\gamma'=\gamma'(\epsilon,\rho)>0$ such that for every Unique Label Cover instance $\mathcal L$ regular on the $V$ side, with any label set size $M$, and every proof $(f_w)_{w\in W}$: if the verifier of §8.1 accepts with probability
--   $$\Pr[\mathrm{acc}]\ \ge\ \frac{\arccos\rho}{\pi}+\epsilon,$$
--   then $\mathrm{OPT}(\mathcal L)\ge\gamma'$.
--
--   The paper's value is $\gamma'=(\epsilon/2)(\delta/2)(\delta/2k)$ with $\delta,k$ from Proposition 7.5. Because $\gamma'$ does not depend on $M$, the Unique Games Conjecture can be applied with soundness $\gamma<\gamma'$.
--
--   **Formalization Note.** The Majority Is Stablest theorem, which the paper cites from [45], enters as the hypothesis `MajorityIsStablest`. $\gamma'$ is chosen before the instance, so it depends on $(\epsilon,\rho)$ only. $V$-regularity is the paper's assumption of §8.1.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 19–20, §8.3 Soundness

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_MIS
import Definitions.Def_OptInapprox_MaxCut_Verifier

namespace OptInapprox.MaxCut

theorem soundness_8_3 (hMIS : MajorityIsStablest) (ρ : ℝ) (hρ₁ : -1 < ρ) (hρ₂ : ρ < 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ γ' : ℝ, 0 < γ' ∧ ∀ L : ULC, L.IsVRegular → ∀ F : Fin L.nW → (Fin L.M → Bool) → Bool,
      Real.arccos ρ / Real.pi + ε ≤ accProb L ρ F → γ' ≤ L.OPT := by sorry

end OptInapprox.MaxCut
