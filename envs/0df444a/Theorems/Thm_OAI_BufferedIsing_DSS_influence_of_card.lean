-- Prove2me | Theorems.Thm_OAI_BufferedIsing_DSS_influence_of_card
-- name    : OAI.BufferedIsing.DSS.influence_of_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:29:47.550676+00:00
-- url     : https://prove2.me/theorems/5d7545c7-a7c3-4d14-8d85-d89ce59d1f92
-- title:
--   Influence inequality: background fields do not increase the effect of a nonnegative field perturbation
-- statement:
--   Let $V$ be a finite set and $J=(J_{uw})_{u,w\in V}$ a real coupling array; both $J_{uw}$ and $J_{wu}$ enter the energy, and diagonal entries only contribute constants. For a field $f\in\mathbb{R}^V$ the Ising Gibbs measure on $\{-1,+1\}^V$ gives $\sigma$ probability proportional to $e^{\mathcal H_{J,f}(\sigma)}$, where $\mathcal H_{J,f}(\sigma)=\sum_{u\in V}\sum_{w\in V}J_{uw}\sigma_u\sigma_w+\sum_{u\in V}f_u\sigma_u$, and $\langle\cdot\rangle_{J,f}$ denotes its expectation.
--
--   **Theorem.** For every finite set $V$ and every coupling array $J$ with $J_{uw}\ge0$ for all $u,w\in V$, the following *influence bound* holds: for all fields $g,h\in\mathbb{R}^V$ with $h_u\ge0$ for every $u\in V$, and every site $o\in V$,
--   $$
--   \langle\sigma_o\rangle_{J,g+h}-\langle\sigma_o\rangle_{J,g-h}\le\langle\sigma_o\rangle_{J,h}-\langle\sigma_o\rangle_{J,-h}.
--   $$
--
--   The left side measures how much the magnetization at $o$ moves when a nonnegative perturbation is switched from $-h$ to $+h$ on top of an arbitrary background field $g$ of any signs; the inequality says that this influence is largest when $g=0$. Applied to the systems obtained by conditioning on one spin, it yields that arbitrary external fields do not increase the spin covariance above the zero-field correlation, $\langle\sigma_u\sigma_v\rangle_{J,g}-\langle\sigma_u\rangle_{J,g}\langle\sigma_v\rangle_{J,g}\le\langle\sigma_u\sigma_v\rangle_{J,0}$.
--
--   **Formalization Note** The statement is phrased for induction: for every `n : ℕ`, every type `V : Type u` with a `Fintype` instance and `Fintype.card V = n`, and every `J : V → V → ℝ` with nonnegative entries, `InfluenceBound J` holds, where `InfluenceBound J` is exactly the displayed inequality for all `g h` with `0 ≤ h` (pointwise) and all `o`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Influence.lean#L155-L217

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure
import Definitions.Def_OAI_Probability_Ising_Interpolation
import Definitions.Def_OAI_Probability_Ising_FieldUpdate
import Definitions.Def_OAI_Probability_Ising_Influence

open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V]

theorem OAI.BufferedIsing.DSS.influence_of_card (n : ℕ) :
    ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ (J : V → V → ℝ), (∀ u v, 0 ≤ J u v) → InfluenceBound J := by sorry
