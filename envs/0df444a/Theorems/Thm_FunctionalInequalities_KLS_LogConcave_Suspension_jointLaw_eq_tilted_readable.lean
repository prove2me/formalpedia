-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_jointLaw_eq_tilted_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw_eq_tilted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:09.66738+00:00
-- url     : https://prove2.me/theorems/a3adf66f-9b93-4f82-ab91-3e0f0b7f991d
-- title:
--   Suspension Joint Law As A Tilted Lebesgue Measure
-- statement:
--   This formalizes the density identity (109) in the proof of Proposition 7.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 28.
--
--   Let $V,f:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}n)\to\mathbb R$ be measurable, let $\beta>0$, and assume $e^{-V}$ is integrable with respect to Lebesgue measure. Let $\mu$ be the probability measure obtained by tilting Lebesgue measure by $-V$. For every $N\in\mathbb N$, the joint law formed from $N$ independent copies with law $\mu$ and an independent Laplace variable of parameter $\beta$ equals the tilted Lebesgue measure on the joint space with potential
--   $$W_N(p)=\sum_{i=1}^N V(x_i)+\beta\left|\sigma_\beta s-\frac1{\sqrt N}\sum_{i=1}^N f(x_i)\right|,$$
--   where $s=p(\operatorname{none})$, $x_i$ is the coordinate indexed by `some (i,j)`, and $\sigma_\beta=\sqrt{1+2/\beta^2}$.
--
--   In Lean notation, the conclusion is the equality between `jointLaw` and `Measure.tilted` by the negative of `potential`. This identifies the suspension distribution with a normalized tilted Lebesgue law and is used in subsequent log-concavity arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem jointLaw_eq_tilted {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {β : ℝ} (hβ : 0 < β)
--       (hV : Measurable V) (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-V x))) :
--       jointLaw (volume.tilted fun x => -V x) f β (sigma β) N =
--         (volume : Measure (JointSpace N n)).tilted fun p =>
--           -potential V f β (sigma β) N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Density`](https://prove2.me/theorems/34f067f9-b370-4131-a2be-776da314cea2).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`KLS/BKL/Suspension/Basic`](https://prove2.me/theorems/aaa7527c-3ccd-45dd-876d-0915bc183526).
--
--   Supporting theorems: [`lintegral_pi_prod_fin`](https://prove2.me/theorems/dd8d5725-3056-4089-9664-4a524cef8983), [`map_density_shift_scale`](https://prove2.me/theorems/09fdc8e8-bedc-44df-98aa-24cf3f553bd2).
--
--   Previous: [`map_density_shift_scale`](https://prove2.me/theorems/09fdc8e8-bedc-44df-98aa-24cf3f553bd2).
--
--   [Source excerpt, lines 278–282](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Density.lean#L278-L282) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Density.lean#L277-L367 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Density`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw_eq_tilted`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Density

open MeasureTheory FunctionalInequalities.Probability.Line

theorem FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw_eq_tilted_readable {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {β : ℝ} (hβ : 0 < β)
    (hV : Measurable V) (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-V x))) :
    jointLaw (volume.tilted fun x => -V x) f β (sigma β) N =
      (volume : Measure (JointSpace N n)).tilted fun p =>
        -potential V f β (sigma β) N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))) := by sorry
