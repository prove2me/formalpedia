-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_histMoment_mono_tau
-- name    : IntMul.Kappa.R8.histMoment_mono_tau
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:06:40.576389+00:00
-- url     : https://prove2.me/theorems/37a521c8-39ec-43fa-ac2d-d80508787eb5
-- title:
--   Child-width moments decrease as the exponent increases
-- statement:
--   **Monotonicity of histogram moments in the exponent.**
--
--   Let $h=((w_i,n_i))_i$ be a finite child-width histogram and let $m\ge 1$ be a width bound. Suppose every width satisfies $0 < w_i \le m$, and let $0 \le \tau_1 \le \tau_2$. Then
--   $$\mathrm{histMoment}(h,m,\tau_2)\le \mathrm{histMoment}(h,m,\tau_1),$$
--   that is
--   $$\sum_i n_i\Big(\frac{w_i}{m}\Big)^{\tau_2}\le \sum_i n_i\Big(\frac{w_i}{m}\Big)^{\tau_1}.$$
--
--   Indeed each base $w_i/m$ lies in $(0,1]$, so $x\mapsto x^\tau$ is antitone in $\tau$ for such $x$, and the claim is the corresponding termwise comparison.
--
--   **Use in round eight.** The stopped bit saving $a_b=(1-\theta)a^*+\theta a_{\mathrm{old}}$ lies between $a_{\mathrm{old}}$ and $a^*$. Whenever $a_b\le a^*$ one has $1-a_b\ge 1-a^*$, so this lemma upgrades the certified bound
--   $$\mathrm{histMoment}(\mathrm{Jain.bitR8},529,1-a^*)<104719230$$
--   to the assembly exponent $\tau=1-a_b$ needed by the parametric machine assembly and by `jain_round8_framework`. The symmetric comparison with the round-seven plain bit histogram covers $a_b\le a_{\mathrm{old}}$.
--
--   **Formalization Note.** `histMoment` is from `IntMul_KappaFramework`.
-- source:
--   Standard real analysis for x^τ on (0,1]; applied as in S. Jain, integer-mult-kappa, https://github.com/Swapnil-jain/integer-mult-kappa/tree/5868dc701a9bec375c9dc5391d992ab3b8c35f3f — README 'Round eight' (stopped mix a_b=(1-theta)a*+theta a_old, theta=1/1000) and the moment hypotheses of Prove2me theorem IntMul.Kappa.jain_round8_framework; histMoment from Def_IntMul_KappaFramework

import Definitions.Def_IntMul_KappaFramework

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8

open IntMul.Kappa

/-- For histograms with every width in `(0, m]`, raising the moment exponent weakly decreases the moment. -/
theorem histMoment_mono_tau (h : List (ℕ × ℕ)) (m : ℕ) (τ₁ τ₂ : ℝ)
    (hm : 0 < m)
    (hw : ∀ p ∈ h, 0 < p.1 ∧ p.1 ≤ m)
    (hτ : 0 ≤ τ₁) (hle : τ₁ ≤ τ₂) :
    histMoment h m τ₂ ≤ histMoment h m τ₁ := by
  sorry

end IntMul.Kappa.R8
