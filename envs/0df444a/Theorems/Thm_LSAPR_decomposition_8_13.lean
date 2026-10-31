-- Prove2me | Theorems.Thm_LSAPR_decomposition_8_13
-- name    : LSAPR.decomposition_8_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:16.018944+00:00
-- url     : https://prove2.me/theorems/97ff6fb5-73e2-4e32-8eaa-dd1b31169b06
-- title:
--   (8), (11), (13) — the pathwise expansion $\theta_n-\theta^\star=\tilde\theta^{(\mathrm{tr})}_n+J^{(0)}_n+J^{(1)}_n+H^{(1)}_n$
-- statement:
--   Let $\bar{\mathbf A}\theta^\star=\bar{\mathbf b}$, $\alpha>0$, $\theta_0\in\mathbb R^d$, and let $(Z_k)$ be any sequence in $\mathsf Z$. Let $\theta_n$ be the LSA iterates (1), $\tilde\theta^{(\mathrm{tr})}_n=\Gamma^{(\alpha)}_{1:n}(\theta_0-\theta^\star)$ the transient term (4), and let $J^{(0)},H^{(0)},J^{(1)},H^{(1)}$ be defined by the recursions (9), (10), (12). Then for every $n\in\mathbb N$,
--   $$\theta_n-\theta^\star=\tilde\theta^{(\mathrm{tr})}_n+J^{(0)}_n+H^{(0)}_n,\qquad H^{(0)}_n=J^{(1)}_n+H^{(1)}_n,$$
--   and consequently
--   $$\theta_n-\theta^\star=\tilde\theta^{(\mathrm{tr})}_n+J^{(0)}_n+J^{(1)}_n+H^{(1)}_n.$$
--
--   The paper calls the last display the cornerstone of its analysis. No probability is involved: the identities hold along every path.
--
--   Differences from the source:
--   - encoding: (8) is about θ̃^(fl)_n, with θ_n − θ⋆ = θ̃^(tr)_n + θ̃^(fl)_n (p.3) → the first clause states θ_n − θ⋆ = tr + J⁽⁰⁾ + H⁽⁰⁾ directly; reason: θ̃^(fl)_n is not a separate Lean object; substituting (8) in the display of p.3 gives this clause
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, (8) p.4, (11) and (13) p.5

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- The pathwise error expansions (8), (11) and (13), arXiv:2207.04475v2, pp.3–5: along every
sample path and for every `n`, with `θ̃^{(tr)}_n = Γ^{(α)}_{1:n}(θ₀ - θ⋆)` ((4), p.3) and
`θ̃^{(fl)}_n = J^{(0)}_n + H^{(0)}_n`,
`θ_n - θ⋆ = θ̃^{(tr)}_n + J^{(0)}_n + H^{(0)}_n` and `H^{(0)}_n = J^{(1)}_n + H^{(1)}_n`, hence
(13) `θ_n - θ⋆ = θ̃^{(tr)}_n + J^{(0)}_n + J^{(1)}_n + H^{(1)}_n`. -/
theorem decomposition_8_13 {d : ℕ} {Z : Type*} [MeasurableSpace Z] (π : Measure Z)
    (A : Z → Mat d) (b : Z → Vec d) (θstar : Vec d)
    (hsol : matApply (Abar π A) θstar = bbar π b)
    (α : ℝ) (hα : 0 < α) (θ0 : Vec d) (Zpath : ℕ → Z) (n : ℕ) :
    lsaIter α A b θ0 Zpath n - θstar =
        matApply (Gamma α A Zpath 1 n) (θ0 - θstar)
          + J0 (Abar π A) (epsNoise π A b θstar) α Zpath n
          + H0 (Abar π A) A (epsNoise π A b θstar) α Zpath n ∧
      H0 (Abar π A) A (epsNoise π A b θstar) α Zpath n =
        J1 (Abar π A) A (epsNoise π A b θstar) α Zpath n
          + H1 (Abar π A) A (epsNoise π A b θstar) α Zpath n ∧
      lsaIter α A b θ0 Zpath n - θstar =
        matApply (Gamma α A Zpath 1 n) (θ0 - θstar)
          + J0 (Abar π A) (epsNoise π A b θstar) α Zpath n
          + J1 (Abar π A) A (epsNoise π A b θstar) α Zpath n
          + H1 (Abar π A) A (epsNoise π A b θstar) α Zpath n := by sorry

end LSAPR
