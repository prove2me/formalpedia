-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_regret_decomposition
-- name    : LinParamBandits.UEGeneral.regret_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:27.801371+00:00
-- url     : https://prove2.me/theorems/621010ff-cc7f-4e9b-bd8f-64f75e157dc0
-- title:
--   Lemma B.8 — regret decomposition
-- statement:
--   Consider a run of the UE policy under Assumption 1. For all $T \ge r+1$ and $z \in \mathbb R^r$,
--   $$\mathrm{Regret}(z, T, \mathrm{UE}) \le 2\bar u(r+2)\|z\| + 2\alpha\sqrt r\,(\log T)\sqrt T\;\mathbb E\left[\sqrt{\sum_{t=r}^{T-1}\|U_{t+1}\|^2_{C_t}} \;\middle|\; Z = z\right].$$
--
--   The first term covers the $r$ initialization periods and the rare periods in which Lemma B.7's event fails; the second reduces the regret to the growth of the weighted arm norms, bounded in Lemmas B.10 and B.11.
--
--   **Formalization Note** The statement is about a run of the UE policy (`IsUE`) under Assumption 1 (`Assumption1`) on a compact nonempty arm set $\mathcal U_r \subset \mathbb R^r$, $r \ge 2$, with noise laws given by a Markov kernel $\nu$ (the law of $W^u_t$ is $\nu(u)$ for every $t$). "$\Pr\{\cdot \mid Z = z\}$" is the law `histMeasure ν z ψ t` of the history $(U_1, X_1, \dots, U_t, X_t)$ with the parameter fixed to $z$; $U_{t+1}$ is `ψ.act t h`. $C_t$ is `Cmat`, the inverse of the design matrix $\sum_{s \le t} U_s U_s'$, which is positive definite on every history that starts with $b_1, \dots, b_r$ (all histories of a UE run, since $t \ge r$). The expectation on the right is the Bochner integral over `histMeasure ν z ψ T` of $\sqrt{\sum_{t=r}^{T-1}\|U_{t+1}\|^2_{C_t}}$, written with `potential (armSeq h) t`; the integrand is nonnegative and bounded on the support, and a junk value $0$ would only make the bound harder.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma B.8, p. 36

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Lemma B.8 (p. 36): regret decomposition. -/
theorem regret_decomposition {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (T : ℕ) (hT : r + 1 ≤ T) (z : LinParamBandits.LowerBound.Vec r) :
    regret ν 𝒰 ψ z T ≤
      2 * ubar * ((r : ℝ) + 2) * ‖z‖ +
        2 * alpha σ₀ ubar lam0 * Real.sqrt r * Real.log T * Real.sqrt T *
          ∫ h, Real.sqrt (∑ t ∈ Finset.Ico r T, potential (armSeq h) t)
            ∂(histMeasure ν z ψ T) := by sorry

end LinParamBandits.UEGeneral
