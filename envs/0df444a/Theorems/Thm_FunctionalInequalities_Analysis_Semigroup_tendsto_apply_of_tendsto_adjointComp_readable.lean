-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_tendsto_apply_of_tendsto_adjointComp_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:06.245493+00:00
-- url     : https://prove2.me/theorems/89a4caec-afca-4ac9-a5f0-98cc15c7d63d
-- title:
--   Graph Convergence Transfers Through a Closed Operator
-- statement:
--   This is a graph-convergence lemma for $T^\dagger T$.
--
--   Let $H_0,H_1$ be real inner-product spaces, let $T:H_0\to H_1$ be a linear partial map, and assume that $D(T)$ is dense in $H_0$. Let $x_n\in D(T^\dagger T)$ and $y\in D(T^\dagger T)$. If
--   1. $x_n\to y$ in $H_0$, and
--   2. $T^\dagger T x_n\to T^\dagger T y$ in $H_0$,
--
--   then
--
--   $$
--   Tx_n\longrightarrow Ty.
--   $$
--
--   This is a technical von Neumann-type continuity statement for the graph of $T^\dagger T$.
--
--   **Formalization Note.** The sequence is indexed by $\mathbb N$, and the operator values are represented using subtype witnesses for domain membership.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_apply_of_tendsto_adjointComp {T : H₀ →ₗ.[ℝ] H₁}
--       (hd : Dense (T.domain : Set H₀)) {x : ℕ → (adjointComp T).domain}
--       {y : (adjointComp T).domain} (h0 : Tendsto (fun n => (x n : H₀)) atTop (𝓝 (y : H₀)))
--       (h1 : Tendsto (fun n => adjointComp T (x n)) atTop (𝓝 (adjointComp T y))) :
--       Tendsto (fun n => T ⟨(x n : H₀), (x n).2.2⟩) atTop (𝓝 (T ⟨(y : H₀), y.2.2⟩))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/VonNeumann`](https://prove2.me/theorems/de8bc764-27c8-4eea-80bc-26a005cde179).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a).
--
--   [Source excerpt, lines 203–207](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean#L203-L207) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean#L200-L223 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.VonNeumann`, declaration `FunctionalInequalities.Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_VonNeumann

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
open Filter Topology

theorem FunctionalInequalities.Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp_readable {T : H₀ →ₗ.[ℝ] H₁}
    (hd : Dense (T.domain : Set H₀)) {x : ℕ → (adjointComp T).domain}
    {y : (adjointComp T).domain} (h0 : Tendsto (fun n => (x n : H₀)) atTop (𝓝 (y : H₀)))
    (h1 : Tendsto (fun n => adjointComp T (x n)) atTop (𝓝 (adjointComp T y))) :
    Tendsto (fun n => T ⟨(x n : H₀), (x n).2.2⟩) atTop (𝓝 (T ⟨(y : H₀), y.2.2⟩)) := by sorry
