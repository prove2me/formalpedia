-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_radius_large_deviation
-- name    : LinParamBandits.UEGeneral.radius_large_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:25.955021+00:00
-- url     : https://prove2.me/theorems/ab6ca709-c824-4740-8e17-3b61a116332d
-- title:
--   Lemma B.6 — large deviation inequalities for the uncertainty radius
-- statement:
--   Consider a run of the UE policy under Assumption 1 and let $\alpha = 4\sigma_0\kappa_0^2$. For every arm $u \in \mathcal U_r$ and every $t \ge r$,
--   $$\Pr\Big\{u'(\widehat Z_t - z) > R^u_t \,\Big|\, Z = z\Big\} \le \frac{1}{t^2},$$
--   and for every $x \in \mathbb R^r$,
--   $$\Pr\Big\{(U_{t+1} - x)'(\widehat Z_t - z) > \alpha\sqrt{\log t}\sqrt{\min\{r\log t, |\mathcal U_r|\}}\,\|U_{t+1} - x\|_{C_t} \,\Big|\, Z = z\Big\} \le \frac{1}{t^2}.$$
--
--   The lemma explains the choice of $\alpha$ and of the uncertainty radius: the probability of overestimating an arm's reward by more than its radius is at most $1/t^2$, which is summable over $t$.
--
--   **Formalization Note** The statement is about a run of the UE policy (`IsUE`) under Assumption 1 (`Assumption1`) on a compact nonempty arm set $\mathcal U_r \subset \mathbb R^r$, $r \ge 2$, with noise laws given by a Markov kernel $\nu$ (the law of $W^u_t$ is $\nu(u)$ for every $t$). "$\Pr\{\cdot \mid Z = z\}$" is the law `histMeasure ν z ψ t` of the history $(U_1, X_1, \dots, U_t, X_t)$ with the parameter fixed to $z$; $U_{t+1}$ is `ψ.act t h`. $C_t$ is `Cmat`, the inverse of the design matrix $\sum_{s \le t} U_s U_s'$, which is positive definite on every history that starts with $b_1, \dots, b_r$ (all histories of a UE run, since $t \ge r$). $\min\{r\log t, |\mathcal U_r|\}$ is `width`, equal to $r\log t$ for an infinite arm set; `radiusFactor 𝒰 σ₀ ubar lam0 t` is $\alpha\sqrt{\log t}\sqrt{\min\{r\log t, |\mathcal U_r|\}}$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma B.6, p. 34

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Lemma B.6 (p. 34): large deviation inequalities for the uncertainty radius. -/
theorem radius_large_deviation {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (t : ℕ) (ht : r ≤ t) (z : LinParamBandits.LowerBound.Vec r) :
    (∀ u ∈ 𝒰, histMeasure ν z ψ t
        {h | radius 𝒰 σ₀ ubar lam0 h u < inner ℝ u (Zhat h - z)} ≤
      ENNReal.ofReal (1 / (t : ℝ) ^ 2)) ∧
    (∀ x : LinParamBandits.LowerBound.Vec r, histMeasure ν z ψ t
        {h | radiusFactor 𝒰 σ₀ ubar lam0 t * wnorm (Cmat (armsOf h)) (ψ.act t h - x) <
          inner ℝ (ψ.act t h - x) (Zhat h - z)} ≤
      ENNReal.ofReal (1 / (t : ℝ) ^ 2)) := by sorry

end LinParamBandits.UEGeneral
