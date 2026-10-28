-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_logConcave_jointLaw_of_eq_tilted_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_jointLaw_of_eq_tilted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:35.680129+00:00
-- url     : https://prove2.me/theorems/91e4e9b1-0b51-481d-b310-130f8697a3a8
-- title:
--   Log-Concavity of the Joint Law Given Its Tilted-Law Identification
-- statement:
--   This conditional lemma states log-concavity of the suspension joint law when its tilted-Lebesgue representation is supplied.
--
--   Let $n,N\in\mathbb N$, $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), and $V,f:E\to\mathbb R$. Let $a,M,\beta\in\mathbb R$. Assume:
--   1. $\beta>0$, and $V,f$ are $C^2$.
--   2. $D^2V(x)[v,v]\ge a\|v\|^2$ for all $x,v$, and $\|D(Df)(x)\|\le M$ for all $x$ (`bilinearIteratedFDerivTwo`, `fderiv`).
--   3. $(\beta/\sqrt N)M\le a$.
--
--   Write $\mu=\operatorname{vol}_E.\operatorname{tilted}(-V)$ (`Measure.tilted`), $\sigma_\beta=\sqrt{1+2/\beta^2}$ (`sigma`), and $\lambda=$ `jointLaw` $\mu\ f\ \beta\ \sigma_\beta\ N$. Its Euclidean target $H=$ `JointSpace` $N\ n$ has coordinates $p_0$ and $p_{ij}$; put $x_i=(p_{ij})_j$. Assume additionally that $\lambda$ is a probability measure and
--   $$
--   \lambda=\operatorname{vol}_H.\operatorname{tilted}\bigl(p\mapsto-W_N(p_0,(x_i)_i)\bigr),
--   \qquad W_N=\text{`potential`}\ V\ f\ \beta\ \sigma_\beta\ N.
--   $$
--   Then the probability measure represented by $\lambda$ satisfies
--   $$
--   \operatorname{LogConcave}(\lambda).
--   $$
--
--   Here `KLS.LogConcave` is the formal log-concavity predicate. The measure identification and probability property are hypotheses, not conclusions; no $N>0$ assumption is imposed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem logConcave_jointLaw_of_eq_tilted {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ)
--       {a M β : ℝ} (hβ : 0 < β) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
--       (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
--       (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
--       (heq : jointLaw (volume.tilted fun x => -V x) f β (sigma β) N =
--         (volume : Measure (JointSpace N n)).tilted fun p =>
--           -potential V f β (sigma β) N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))))
--       (h : IsProbabilityMeasure (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)) :
--       KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (JointSpace N n))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/BKL/Suspension/Basic`](https://prove2.me/theorems/aaa7527c-3ccd-45dd-876d-0915bc183526).
--
--   Supporting theorems: [`convexOn_potential`](https://prove2.me/theorems/8bd14eff-e39b-41f3-a887-8c1cbe3d5c1e), [`isBorellDensity_of_eq_tilted`](https://prove2.me/theorems/0d7194a7-857d-46cc-b91c-8366be9b61de).
--
--   Next: [`cumulantBound_jointSpace`](https://prove2.me/theorems/88c575f1-15b2-4a92-828b-6fef20c27f09).
--
--   [Source excerpt, lines 152–160](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Law.lean#L152-L160) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Law.lean#L151-L224 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Law`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_jointLaw_of_eq_tilted`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Law

open MeasureTheory

theorem FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_jointLaw_of_eq_tilted_readable {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ)
    {a M β : ℝ} (hβ : 0 < β) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (heq : jointLaw (volume.tilted fun x => -V x) f β (sigma β) N =
      (volume : Measure (JointSpace N n)).tilted fun p =>
        -potential V f β (sigma β) N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))))
    (h : IsProbabilityMeasure (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)) :
    KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (JointSpace N n)) := by sorry
