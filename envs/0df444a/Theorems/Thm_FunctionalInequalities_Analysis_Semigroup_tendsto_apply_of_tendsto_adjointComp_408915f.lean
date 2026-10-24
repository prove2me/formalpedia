-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_tendsto_apply_of_tendsto_adjointComp_408915f
-- name    : FunctionalInequalities.Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:03.150463+00:00
-- url     : https://prove2.me/theorems/86551778-9e53-4e05-9cf7-76c058e116bc
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean#L200-L223 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.VonNeumann`, declaration `FunctionalInequalities.Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace LinearPMap
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Semigroup
end FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
open Filter Topology

theorem FunctionalInequalities.Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp_408915f {T : H₀ →ₗ.[ℝ] H₁}
    (hd : Dense (T.domain : Set H₀)) {x : ℕ → (adjointComp T).domain}
    {y : (adjointComp T).domain} (h0 : Tendsto (fun n => (x n : H₀)) atTop (𝓝 (y : H₀)))
    (h1 : Tendsto (fun n => adjointComp T (x n)) atTop (𝓝 (adjointComp T y))) :
    Tendsto (fun n => T ⟨(x n : H₀), (x n).2.2⟩) atTop (𝓝 (T ⟨(y : H₀), y.2.2⟩)) := by sorry
