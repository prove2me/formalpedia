-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_cumulantBound_jointSpace_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_jointSpace_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:06.353264+00:00
-- url     : https://prove2.me/theorems/88c575f1-15b2-4a92-828b-6fef20c27f09
-- title:
--   Cumulant Bound On The Suspension Joint Space
-- statement:
--   This formalizes the joint-space adapter used in Proposition 7.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 28.
--
--   Let $N,n,d\in\mathbb N$ and $b\in\mathbb R$. Assume `CumulantBound d b`, and let $\nu$ be an isotropic log-concave probability measure on
--   $$\operatorname{JointSpace}(N,n)=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Option}(\operatorname{Fin}N\times\operatorname{Fin}n)).$$
--   For every $u$ in this joint space, the coordinate cumulants satisfy
--   $$\sum_J\kappa_{d+1}^\nu\bigl(u,e_{J_1},\ldots,e_{J_d}\bigr)^2
--   \le b\|u\|^2,$$
--   where the sum ranges over functions $J:\operatorname{Fin}d\to\operatorname{Option}(\operatorname{Fin}N\times\operatorname{Fin}n)$ and the $e_{J_i}$ are the corresponding coordinate basis vectors.
--
--   The declaration transports a cumulant bound through the coordinate equivalence between the joint space and a standard Euclidean space. It is a technical reuse lemma for suspension arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulantBound_jointSpace {N n d : ℕ} {b : ℝ} (hb : CumulantBound d b)
--       {ν : ProbabilityMeasure (JointSpace N n)} (hiso : KLS.Isotropic ν) (hlc : KLS.LogConcave ν)
--       (u : JointSpace N n) :
--       ∑ J : Fin d → Option (Fin N × Fin n),
--         cumulant (ν : Measure (JointSpace N n)) (d + 1)
--           (Fin.cons u fun k => EuclideanSpace.basisFun _ ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`cumulant_map_linearIsometryEquiv`](https://prove2.me/theorems/2c6f9c5b-4b75-4b42-9954-60d10b0a3552), [`Isotropic.map_linearIsometryEquiv`](https://prove2.me/theorems/2a04e022-1e2a-44a3-9511-86cbce831c79).
--
--   Previous: [`logConcave_jointLaw_of_eq_tilted`](https://prove2.me/theorems/91e4e9b1-0b51-481d-b310-130f8697a3a8).
--
--   [Source excerpt, lines 281–286](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Law.lean#L281-L286) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Law.lean#L276-L308 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Law`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_jointSpace`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Law

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery

theorem FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_jointSpace_readable {N n d : ℕ} {b : ℝ} (hb : CumulantBound d b)
    {ν : ProbabilityMeasure (JointSpace N n)} (hiso : KLS.Isotropic ν) (hlc : KLS.LogConcave ν)
    (u : JointSpace N n) :
    ∑ J : Fin d → Option (Fin N × Fin n),
      cumulant (ν : Measure (JointSpace N n)) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun _ ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2 := by sorry
