-- Prove2me | Theorems.Thm_OAI_BufferedIsing_DSS_mean_field_update
-- name    : OAI.BufferedIsing.DSS.mean_field_update
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:26:05.966817+00:00
-- url     : https://prove2.me/theorems/74c20ce4-d52c-4d21-b0e2-06dddda44741
-- title:
--   A field added at a site updates its magnetization by the hyperbolic-tangent addition law
-- statement:
--   Let $V$ be a finite set and $J=(J_{uw})_{u,w\in V}$ a real coupling array; both $J_{uw}$ and $J_{wu}$ enter the energy, and diagonal entries only contribute constants. For a field $f\in\mathbb{R}^V$ the Ising Gibbs measure on $\{-1,+1\}^V$ gives $\sigma$ probability proportional to $e^{\mathcal H_{J,f}(\sigma)}$, where $\mathcal H_{J,f}(\sigma)=\sum_{u\in V}\sum_{w\in V}J_{uw}\sigma_u\sigma_w+\sum_{u\in V}f_u\sigma_u$, and $\langle\cdot\rangle_{J,f}$ denotes its expectation. For $v\in V$ and $t\in\mathbb{R}$ let $t\delta_v$ be the field equal to $t$ at $v$ and $0$ elsewhere.
--
--   **Theorem.** For every coupling array $J$ (of arbitrary signs), every field $h\in\mathbb{R}^V$, every site $v\in V$ and every $t\in\mathbb{R}$,
--   $$
--   \langle\sigma_v\rangle_{J,h+t\delta_v}=\frac{\langle\sigma_v\rangle_{J,h}+\tanh t}{1+\langle\sigma_v\rangle_{J,h}\tanh t}.
--   $$
--
--   Since $\langle\sigma_v\rangle_{J,h}$ lies strictly between $-1$ and $1$, it can be written as $\tanh x$, and the formula says that the new magnetization is $\tanh(x+t)$: a field added at a site shifts the inverse hyperbolic tangent of that site's own magnetization by exactly $t$, whatever the rest of the system looks like. This explicit rational update is what makes the single-site induction in the proof of the influence inequality tractable.
--
--   **Formalization Note** $t\delta_v$ is `fieldAt v t` and $\langle\sigma_v\rangle_{J,h}$ is `mean J h v`. No sign condition on $J$ is assumed, and the denominator on the right is always positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/FieldUpdate.lean#L171-L186

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

open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical
variable {V : Type*} [Fintype V]

theorem OAI.BufferedIsing.DSS.mean_field_update (J : V → V → ℝ) (h : V → ℝ) (v : V) (t : ℝ) :
    mean J (h + fieldAt v t) v = (mean J h v + Real.tanh t) /
      (1 + mean J h v * Real.tanh t) := by sorry
