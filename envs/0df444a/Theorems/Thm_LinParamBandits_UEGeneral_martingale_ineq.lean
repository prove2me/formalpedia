-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_martingale_ineq
-- name    : LinParamBandits.UEGeneral.martingale_ineq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:18.834174+00:00
-- url     : https://prove2.me/theorems/a3ae42fb-314e-4da1-9d93-2ce4760a9b28
-- title:
--   Lemma B.4 — martingale inequality for x′M_t
-- statement:
--   Consider a run of the UE policy under Assumption 1 and let $M_t = \sum_{s=1}^t U_sW_s$. For every $x \in \mathbb R^r$, every $t \ge r$ and every $\zeta \ge \sqrt 2$,
--   $$\Pr\Big\{|x'M_t| > \zeta\kappa_0\sigma_0\sqrt{\log t}\,\|x\|_{C_t^{-1}}\Big\} = \Pr\Big\{x'M_tM_t'x > \zeta^2\kappa_0^2\sigma_0^2(\log t)\,(x'C_t^{-1}x)\Big\} \le e^{-\zeta^2/2}.$$
--   Here $C_t^{-1} = \sum_{s=1}^t U_sU_s'$, so $\|x\|_{C_t^{-1}} = \sqrt{\sum_{s=1}^t(x'U_s)^2}$.
--
--   This is the one-direction form of the large deviation inequality for adaptive least squares; Lemma B.5 extends it to all directions at once.
--
--   **Formalization Note** The statement is about a run of the UE policy (`IsUE`) under Assumption 1 (`Assumption1`) on a compact nonempty arm set $\mathcal U_r \subset \mathbb R^r$, $r \ge 2$, with noise laws given by a Markov kernel $\nu$ (the law of $W^u_t$ is $\nu(u)$ for every $t$). "$\Pr\{\cdot \mid Z = z\}$" is the law `histMeasure ν z ψ t` of the history $(U_1, X_1, \dots, U_t, X_t)$ with the parameter fixed to $z$; $U_{t+1}$ is `ψ.act t h`. $C_t$ is `Cmat`, the inverse of the design matrix $\sum_{s \le t} U_s U_s'$, which is positive definite on every history that starts with $b_1, \dots, b_r$ (all histories of a UE run, since $t \ge r$). The probability is taken given $Z = z$, for every $z$ (the paper applies the lemma in this conditional form in the proof of Theorem B.2; the unconditional form follows for every prior). **Corrected slip:** the page states the lemma for $t \ge 1$; its proof uses $\lambda_0 \le \lambda_{\min}(\sum_{s \le t}U_sU_s')$, which needs the $r$ initial arms, and $t \ge r \ge 2$. At $t = 1$ the threshold is $0$ ($\log 1 = 0$) and the printed claim $\Pr\{|x'U_1W_1| > 0\} \le e^{-\zeta^2/2}$ fails for continuous noise. The statement is made for $t \ge r$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma B.4, p. 30 (proof p. 31)

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Lemma B.4 (p. 30): martingale inequality, stated for `t ≥ r` (the printed `t ≥ 1` is a
slip, see the Formalization Note) and given `Z = z`. -/
theorem martingale_ineq {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (x z : LinParamBandits.LowerBound.Vec r) (t : ℕ) (ht : r ≤ t) (ζ : ℝ) (hζ : Real.sqrt 2 ≤ ζ) :
    histMeasure ν z ψ t
        {h | ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) *
            wnorm (design (armsOf h)) x < |inner ℝ x (Mvec z h)|} =
      histMeasure ν z ψ t
        {h | ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t *
            quadForm (design (armsOf h)) x < inner ℝ x (Mvec z h) ^ 2} ∧
    histMeasure ν z ψ t
        {h | ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t *
            quadForm (design (armsOf h)) x < inner ℝ x (Mvec z h) ^ 2} ≤
      ENNReal.ofReal (Real.exp (-ζ ^ 2 / 2)) := by sorry

end LinParamBandits.UEGeneral
