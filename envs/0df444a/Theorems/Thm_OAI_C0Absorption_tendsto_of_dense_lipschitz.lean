-- Prove2me | Theorems.Thm_OAI_C0Absorption_tendsto_of_dense_lipschitz
-- name    : OAI.C0Absorption.tendsto_of_dense_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T21:56:12.212878+00:00
-- url     : https://prove2.me/theorems/e2e6fa80-6795-4198-8797-5f93a4a4b986
-- title:
--   Equi-Lipschitz convergence on a dense set implies convergence everywhere
-- statement:
--   Let $f_n,g:X\to Y$ be $K$-Lipschitz maps between pseudo-metric spaces, and let $(d_a)$ have dense range in $X$. If $f_n(d_a)\to g(d_a)$ for every $a$, then
--   $$
--   f_n(x)\to g(x)\qquad\text{for every }x\in X .
--   $$
--
--   Uniform Lipschitz bounds upgrade convergence on a dense set to pointwise convergence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Lists.lean#L181-L199

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset

theorem OAI.C0Absorption.tendsto_of_dense_lipschitz {A X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (d : A → X) (hd : DenseRange d) (f : ℕ → X → Y) (g : X → Y) (K : ℝ≥0)
    (hf : ∀ n, LipschitzWith K (f n)) (hg : LipschitzWith K g)
    (h : ∀ a, Filter.Tendsto (fun n => f n (d a)) Filter.atTop (nhds (g (d a))))
    (x : X) : Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x)) := by sorry
