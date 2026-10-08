-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_inst_regret_bound
-- name    : LinParamBandits.UEGeneral.inst_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:27.712118+00:00
-- url     : https://prove2.me/theorems/499c2e79-d099-4e00-b7d1-db5d32d420f4
-- title:
--   Lemma B.7 — instantaneous regret bound
-- statement:
--   Consider a run of the UE policy under Assumption 1 and let $Q_{t+1}(z) = \max_{v \in \mathcal U_r}v'z - U_{t+1}'z$ be the instantaneous regret in period $t+1$ given $Z = z$. For all $t \ge r$ and $z \in \mathbb R^r$,
--   $$\Pr\Big\{Q_{t+1}(z) > 2\alpha\sqrt{\log t}\sqrt{\min\{r\log t, |\mathcal U_r|\}}\,\|U_{t+1}\|_{C_t} \,\Big|\, Z = z\Big\} \le \frac{1}{t^2}.$$
--
--   The instantaneous regret is thus, outside an event of probability $1/t^2$, at most twice the uncertainty radius of the arm played; this is the basis of the regret decomposition, Lemma B.8.
--
--   **Formalization Note** The statement is about a run of the UE policy (`IsUE`) under Assumption 1 (`Assumption1`) on a compact nonempty arm set $\mathcal U_r \subset \mathbb R^r$, $r \ge 2$, with noise laws given by a Markov kernel $\nu$ (the law of $W^u_t$ is $\nu(u)$ for every $t$). "$\Pr\{\cdot \mid Z = z\}$" is the law `histMeasure ν z ψ t` of the history $(U_1, X_1, \dots, U_t, X_t)$ with the parameter fixed to $z$; $U_{t+1}$ is `ψ.act t h`. $C_t$ is `Cmat`, the inverse of the design matrix $\sum_{s \le t} U_s U_s'$, which is positive definite on every history that starts with $b_1, \dots, b_r$ (all histories of a UE run, since $t \ge r$). $Q_{t+1}(z)$ is `instRegret 𝒰 z (ψ.act t h)`.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma B.7, p. 35; eq. (9), p. 35

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Lemma B.7 (p. 35): instantaneous regret bound. -/
theorem inst_regret_bound {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (t : ℕ) (ht : r ≤ t) (z : LinParamBandits.LowerBound.Vec r) :
    histMeasure ν z ψ t
        {h | 2 * radiusFactor 𝒰 σ₀ ubar lam0 t * wnorm (Cmat (armsOf h)) (ψ.act t h) <
          instRegret 𝒰 z (ψ.act t h)} ≤
      ENNReal.ofReal (1 / (t : ℝ) ^ 2) := by sorry

end LinParamBandits.UEGeneral
