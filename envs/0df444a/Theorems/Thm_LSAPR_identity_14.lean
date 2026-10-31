-- Prove2me | Theorems.Thm_LSAPR_identity_14
-- name    : LSAPR.identity_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:08.780326+00:00
-- url     : https://prove2.me/theorems/42d4f079-6305-4392-bd97-295e1b59b454
-- title:
--   (14) and (15) — the Polyak–Ruppert identity for $\bar{\mathbf A}(\bar\theta_n-\theta^\star)$
-- statement:
--   Let $\bar{\mathbf A}\theta^\star=\bar{\mathbf b}$, $\alpha>0$, $\theta_0\in\mathbb R^d$, and let $(Z_k)$ be any sequence in $\mathsf Z$. For $n_0<n$, the LSA iterates and their average (1) satisfy
--   $$\bar{\mathbf A}(\bar\theta_n-\theta^\star)=\{\alpha(n-n_0)\}^{-1}(\theta_{n_0}-\theta_n)-(n-n_0)^{-1}\sum_{t=n_0}^{n-1}e(\theta_t,Z_{t+1}),$$
--   where, for all $\theta$ and $z$,
--   $$e(\theta,z)=\tilde{\mathbf A}(z)\theta-\tilde{\mathbf b}(z)=\varepsilon(z)+\tilde{\mathbf A}(z)(\theta-\theta^\star).$$
--
--   The identity splits the averaged error into a boundary term and a sum that is a martingale in the i.i.d. case. The first equality in the definition of $e$ is the Lean definition `eNoise`.
--
--   Differences from the source: none.
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, (14) and (15), p.5

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- The Polyak–Ruppert identity (14) with (15), arXiv:2207.04475v2, p.5: along every sample path,
for `n0 < n`,
`Ā (θ̄_n - θ⋆) = {α (n - n0)}⁻¹ (θ_{n0} - θ_n) - (n - n0)⁻¹ ∑_{t=n0}^{n-1} e(θ_t, Z_{t+1})`,
and `e(θ, z) = Ã(z) θ - b̃(z) = ε(z) + Ã(z)(θ - θ⋆)` for all `θ, z`. -/
theorem identity_14 {d : ℕ} {Z : Type*} [MeasurableSpace Z] (π : Measure Z)
    (A : Z → Mat d) (b : Z → Vec d) (θstar : Vec d)
    (hsol : matApply (Abar π A) θstar = bbar π b)
    (α : ℝ) (hα : 0 < α) (θ0 : Vec d) (Zpath : ℕ → Z) (n0 n : ℕ) (hn : n0 < n) :
    matApply (Abar π A) (prAvg α A b θ0 Zpath n0 n - θstar) =
        (α * ((n : ℝ) - n0))⁻¹ • (lsaIter α A b θ0 Zpath n0 - lsaIter α A b θ0 Zpath n)
          - ((n : ℝ) - n0)⁻¹ • ∑ t ∈ Finset.Ico n0 n,
              eNoise π A b (lsaIter α A b θ0 Zpath t) (Zpath (t + 1)) ∧
      ∀ (θ : Vec d) (z : Z), eNoise π A b θ z =
        epsNoise π A b θstar z + matApply (Atilde π A z) (θ - θstar) := by sorry

end LSAPR
