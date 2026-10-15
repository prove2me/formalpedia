-- Prove2me | Theorems.Thm_OAI_BufferedIsing_DSS_covariance_le_zero_field
-- name    : OAI.BufferedIsing.DSS.covariance_le_zero_field
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:30:47.584538+00:00
-- url     : https://prove2.me/theorems/97d380d0-6771-4be1-88c0-8209c3fb055c
-- title:
--   In a ferromagnetic Ising model, the spin covariance under any external field is at most the zero-field correlation
-- statement:
--   Let $V$ be a finite set, let $J:V\times V\to\mathbb{R}$ be a coupling array with $J(x,y)\ge 0$ for all $x,y\in V$ (ordered pairs, diagonal included), and let $g:V\to\mathbb{R}$ be an arbitrary external field. For a spin configuration $\sigma\in\{-1,+1\}^V$ define the Hamiltonian, and for a function $f$ of the configuration define its Gibbs expectation, by
--
--   $$
--   H_{J,g}(\sigma)=\sum_{x\in V}\sum_{y\in V}J(x,y)\,\sigma_x\sigma_y+\sum_{x\in V}g(x)\,\sigma_x,
--   \qquad
--   \langle f\rangle_{J,g}=\frac{\sum_{\sigma}e^{H_{J,g}(\sigma)}\,f(\sigma)}{\sum_{\sigma}e^{H_{J,g}(\sigma)}},
--   $$
--
--   where $\sigma$ runs over all of $\{-1,+1\}^V$. Each unordered pair $\{x,y\}$ of distinct sites thus interacts with total coupling $J(x,y)+J(y,x)\ge 0$ (a ferromagnetic interaction, with the inverse temperature absorbed into $J$ and $g$), and the diagonal terms $J(x,x)\sigma_x^2=J(x,x)$ are constants.
--
--   **Theorem.** For all sites $u,v\in V$, not necessarily distinct,
--
--   $$
--   \langle\sigma_u\sigma_v\rangle_{J,g}-\langle\sigma_u\rangle_{J,g}\,\langle\sigma_v\rangle_{J,g}\;\le\;\langle\sigma_u\sigma_v\rangle_{J,0},
--   $$
--
--   where the right-hand side is the two-point correlation of the same ferromagnet in zero external field.
--
--   In words: whatever the external field, the covariance (truncated two-point function) of two spins of a finite ferromagnetic Ising model never exceeds their zero-field correlation. For $u=v$ the inequality is the trivial bound $1-\langle\sigma_u\rangle_{J,g}^2\le 1$. For $u\ne v$ it is the key input for showing that external fields cannot increase the effective coupling between two sites, which in turn gives field-uniform comparison bounds for conditional laws of the Ising model on finite graphs.
--
--   **Formalization Note** Spins are Booleans, with `sgn true = 1` and `sgn false = -1`; the Hamiltonian, the Gibbs weight $e^{H_{J,g}}$ and the expectation are `hamiltonian`, `mass` and `average`, and $\langle\sigma_u\rangle_{J,g}$, $\langle\sigma_u\sigma_v\rangle_{J,g}$ are `mean J g u` and `correlation J g u v`. The zero field is the constant function `0`. The coupling array is directed (both $J(x,y)$ and $J(y,x)$ are summed), which allows exact restriction to subsets of sites.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Influence.lean#L260-L274

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

theorem OAI.BufferedIsing.DSS.covariance_le_zero_field (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g : V → ℝ) (u v : V) :
    correlation J g u v - mean J g u * mean J g v ≤ correlation J 0 u v := by sorry
