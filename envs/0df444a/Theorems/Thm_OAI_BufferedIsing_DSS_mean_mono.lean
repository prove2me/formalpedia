-- Prove2me | Theorems.Thm_OAI_BufferedIsing_DSS_mean_mono
-- name    : OAI.BufferedIsing.DSS.mean_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:23:34.159827+00:00
-- url     : https://prove2.me/theorems/277bcfef-14a2-4718-a182-7fdf3c9bb8af
-- title:
--   Ferromagnetic Ising magnetizations are monotone in the external field
-- statement:
--   Let $V$ be a finite set and $J=(J_{uw})_{u,w\in V}$ a real coupling array; both $J_{uw}$ and $J_{wu}$ enter the energy, and diagonal entries only contribute constants. For a field $f\in\mathbb{R}^V$ the Ising Gibbs measure on $\{-1,+1\}^V$ gives $\sigma$ probability proportional to $e^{\mathcal H_{J,f}(\sigma)}$, where $\mathcal H_{J,f}(\sigma)=\sum_{u\in V}\sum_{w\in V}J_{uw}\sigma_u\sigma_w+\sum_{u\in V}f_u\sigma_u$, and $\langle\cdot\rangle_{J,f}$ denotes its expectation.
--
--   **Theorem.** Suppose $J_{uw}\ge0$ for all $u,w\in V$, and let $h,k\in\mathbb{R}^V$ satisfy $h_u\le k_u$ for every $u\in V$. Then for every site $o\in V$,
--   $$
--   \langle\sigma_o\rangle_{J,h}\le\langle\sigma_o\rangle_{J,k}.
--   $$
--
--   This is the classical monotonicity of magnetizations in the external field for ferromagnetic Ising models, a consequence of the FKG inequality. It holds for fields of arbitrary signs and is used repeatedly in the proof of the influence inequality: to order the magnetizations under the fields $g-h\le g+h$, to compare the conditional magnetizations given $\sigma_v=+1$ and $\sigma_v=-1$, and to see that nonnegative fields produce nonnegative magnetizations.
--
--   **Formalization Note** Spins are Booleans, ordered by `false < true` and mapped to $\mp1$ by `sgn`; $\langle\sigma_o\rangle_{J,h}$ is `mean J h o`, the hypothesis $h\le k$ is the pointwise order on functions `V → ℝ`, and $V$ is any type with a `Fintype` instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/GibbsMeasure.lean#L124-L160

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

open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical
variable {V : Type*} [Fintype V]

theorem OAI.BufferedIsing.DSS.mean_mono (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h k : V → ℝ) (hhk : h ≤ k) (o : V) : mean J h o ≤ mean J k o := by sorry
