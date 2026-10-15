-- Prove2me | Theorems.Thm_OAI_BufferedIsing_DSS_pin_comparison_of_removed
-- name    : OAI.BufferedIsing.DSS.pin_comparison_of_removed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:27:31.713845+00:00
-- url     : https://prove2.me/theorems/c5f236da-5772-414d-9c9f-6811cda6dd0a
-- title:
--   Pinned-site comparison from the influence bound on the remaining sites
-- statement:
--   Let $V$ be a finite set and $J=(J_{uw})_{u,w\in V}$ a real coupling array; both $J_{uw}$ and $J_{wu}$ enter the energy, and diagonal entries only contribute constants. For a field $f\in\mathbb{R}^V$ the Ising Gibbs measure on $\{-1,+1\}^V$ gives $\sigma$ probability proportional to $e^{\mathcal H_{J,f}(\sigma)}$, where $\mathcal H_{J,f}(\sigma)=\sum_{u\in V}\sum_{w\in V}J_{uw}\sigma_u\sigma_w+\sum_{u\in V}f_u\sigma_u$, and $\langle\cdot\rangle_{J,f}$ denotes its expectation. Write $m_f(o)=\langle\sigma_o\rangle_{J,f}$ for the magnetization at $o\in V$, and for $v\in V$ and $t\in\mathbb{R}$ write $t\delta_v$ for the field equal to $t$ at $v$ and $0$ elsewhere. For a fixed site $v$ let $m^{\pm}_f(o)=\langle\sigma_o\mid\sigma_v=\pm1\rangle_{J,f}$ be the conditional magnetizations at $o$ given the spin at $v$; in particular $m^{\pm}_f(v)=\pm1$. Let $J'$ be the restriction of $J$ to $(V\setminus\{v\})\times(V\setminus\{v\})$, and write $\langle\cdot\rangle_{J',f'}$ for the corresponding Gibbs expectation on $\{-1,+1\}^{V\setminus\{v\}}$ with a field $f'$ on $V\setminus\{v\}$.
--
--   **Theorem.** Assume $J_{uw}\ge0$ for all $u,w\in V$. Let $g,h\in\mathbb{R}^V$ with $h_u\ge0$ for every $u$, and let $v,o\in V$. Suppose that $J'$ satisfies the influence bound: for all fields $g',h'$ on $V\setminus\{v\}$ with $h'\ge0$ and every site $o'\in V\setminus\{v\}$, $\langle\sigma_{o'}\rangle_{J',g'+h'}-\langle\sigma_{o'}\rangle_{J',g'-h'}\le\langle\sigma_{o'}\rangle_{J',h'}-\langle\sigma_{o'}\rangle_{J',-h'}$. Then
--   $$
--   m^{+}_{g+h}(o)-m^{-}_{g-h}(o)\le m^{+}_{h}(o)-m^{-}_{-h}(o).
--   $$
--
--   This supplies the pinned-comparison hypothesis of the induction step for the influence inequality from the influence bound on the smaller vertex set $V\setminus\{v\}$, which is what makes an induction on the number of sites possible.
--
--   **Formalization Note** $m^{\pm}_f(o)$ is `pinMean J f v true o` and `pinMean J f v false o`, defined as the magnetization at $o$ of the system on $V\setminus\{v\}$ with the restricted couplings and the fields $f_u+(J_{vu}+J_{uv})(\pm1)$, with the spin $\pm1$ inserted at $v$ (for $o=v$ it equals $\pm1$); this is the conditional magnetization described above. The hypothesis on $J'$ is `InfluenceBound (removedCoupling J v)`, where `removedCoupling J v` is $J$ restricted to the subtype `{u : V // u ≠ v}`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Influence.lean#L120-L151

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

theorem OAI.BufferedIsing.DSS.pin_comparison_of_removed (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g h : V → ℝ) (hh : 0 ≤ h) (v o : V)
    (H : InfluenceBound (removedCoupling J v)) :
    pinMean J (g + h) v true o - pinMean J (g - h) v false o ≤
      pinMean J h v true o - pinMean J (-h) v false o := by sorry
