-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_sequentialRelaxation_comp_le_mul_readable
-- name    : FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:21.986792+00:00
-- url     : https://prove2.me/theorems/6442fdfe-7a22-4ff2-a77c-0cf355fd2512
-- title:
--   Scaled Comparison of Sequential Relaxations
-- statement:
--   This is a general comparison principle for sequential relaxations.
--
--   Let $X$ and $Y$ be topological spaces, let $P$ and $Q$ be pre-energies on $X$ and $Y$, let $T:X\to Y$ be continuous, and let $\kappa\in[0,\infty)$ be an `NNReal`. Assume that every test $f$ of $P$ admits a test $g$ of $Q$ such that
--
--   $$
--   Q.\operatorname{toAmbient}(g)=T(P.\operatorname{toAmbient}(f))
--   $$
--
--   and
--
--   $$
--   Q.\operatorname{energy}(g)\le \kappa\,P.\operatorname{energy}(f).
--   $$
--
--   Then, for every $x\in X$ with finite $P$-sequential relaxation,
--
--   $$
--   Q.\operatorname{sequentialRelaxation}(Tx)
--   \le
--   \kappa\,P.\operatorname{sequentialRelaxation}(x).
--   $$
--
--   This reusable lemma transports finite energy comparisons through continuous maps.
--
--   **Formalization Note** Energies and relaxations take values in $[0,\infty]$ (`ENNReal`), while $\kappa$ is coerced from `NNReal`; the finiteness premise excludes a top-valued source relaxation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.PreEnergy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sequentialRelaxation_comp_le_mul {Y : Type*} [TopologicalSpace Y]
--       (Q : PreEnergy Y) (T : X → Y) (hT : Continuous T) (κ : NNReal)
--       (h : ∀ f : P.Test, ∃ g : Q.Test,
--         Q.toAmbient g = T (P.toAmbient f) ∧ (Q.energy g : ENNReal) ≤ κ * P.energy f) (x : X)
--       (hx : P.sequentialRelaxation x ≠ ⊤) :
--       Q.sequentialRelaxation (T x) ≤ κ * P.sequentialRelaxation x
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Relaxation/Basic`](https://prove2.me/theorems/89c7a615-0c3d-45b2-8b60-f8b981228e0a).
--
--   Definition modules: [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765).
--
--   [Source excerpt, lines 113–118](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Relaxation/Basic.lean#L113-L118) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/Basic.lean#L109-L136 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.Basic`, declaration `FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic

universe u v
variable {X : Type u} [TopologicalSpace X] (P : FunctionalInequalities.Energy.PreEnergy X)

theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul_readable {Y : Type*} [TopologicalSpace Y]
    (Q : PreEnergy Y) (T : X → Y) (hT : Continuous T) (κ : NNReal)
    (h : ∀ f : P.Test, ∃ g : Q.Test,
      Q.toAmbient g = T (P.toAmbient f) ∧ (Q.energy g : ENNReal) ≤ κ * P.energy f) (x : X)
    (hx : P.sequentialRelaxation x ≠ ⊤) :
    Q.sequentialRelaxation (T x) ≤ κ * P.sequentialRelaxation x := by sorry
