-- Prove2me | Theorems.Thm_OAI_BufferedIsing_DSS_influence_step
-- name    : OAI.BufferedIsing.DSS.influence_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:26:35.563853+00:00
-- url     : https://prove2.me/theorems/068b816c-d1dc-483d-8a79-94865e4f18f9
-- title:
--   Induction step for the influence inequality: raising the perturbation at one site
-- statement:
--   Let $V$ be a finite set and $J=(J_{uw})_{u,w\in V}$ a real coupling array; both $J_{uw}$ and $J_{wu}$ enter the energy, and diagonal entries only contribute constants. For a field $f\in\mathbb{R}^V$ the Ising Gibbs measure on $\{-1,+1\}^V$ gives $\sigma$ probability proportional to $e^{\mathcal H_{J,f}(\sigma)}$, where $\mathcal H_{J,f}(\sigma)=\sum_{u\in V}\sum_{w\in V}J_{uw}\sigma_u\sigma_w+\sum_{u\in V}f_u\sigma_u$, and $\langle\cdot\rangle_{J,f}$ denotes its expectation. Write $m_f(o)=\langle\sigma_o\rangle_{J,f}$ for the magnetization at $o\in V$, and for $v\in V$ and $t\in\mathbb{R}$ write $t\delta_v$ for the field equal to $t$ at $v$ and $0$ elsewhere. For a fixed site $v$ let $m^{\pm}_f(o)=\langle\sigma_o\mid\sigma_v=\pm1\rangle_{J,f}$ be the conditional magnetizations at $o$ given the spin at $v$; in particular $m^{\pm}_f(v)=\pm1$.
--
--   **Theorem.** Assume $J_{uw}\ge0$ for all $u,w\in V$. Let $g,h\in\mathbb{R}^V$ with $h_u\ge0$ for every $u$, let $v,o\in V$ and $t\ge0$, and suppose:
--
--   1. (influence bound for $h$) for every field $g'\in\mathbb{R}^V$ and every site $o'\in V$: $m_{g'+h}(o')-m_{g'-h}(o')\le m_h(o')-m_{-h}(o')$;
--   2. (pinned comparison at $v$): $m^{+}_{g+h}(o)-m^{-}_{g-h}(o)\le m^{+}_{h}(o)-m^{-}_{-h}(o)$.
--
--   Then
--   $$
--   m_{g+h+t\delta_v}(o)-m_{g-h-t\delta_v}(o)\le m_{h+t\delta_v}(o)-m_{-h-t\delta_v}(o).
--   $$
--
--   This is the induction step of the influence inequality, which asserts that switching a nonnegative perturbation from $-h$ to $+h$ moves a magnetization the most when there is no background field. If the inequality is known for the perturbation $h$ (hypothesis 1) and for the conditional systems pinned at $v$ (hypothesis 2), it follows at the site $o$ for the larger perturbation $h+t\delta_v$. Iterating over the sites where the perturbation is positive proves the full influence inequality.
--
--   **Formalization Note** $m^{\pm}_f(o)$ is `pinMean J f v true o` and `pinMean J f v false o`, defined as the magnetization at $o$ of the system on $V\setminus\{v\}$ with the restricted couplings and the fields $f_u+(J_{vu}+J_{uv})(\pm1)$, with the spin $\pm1$ inserted at $v$ (for $o=v$ it equals $\pm1$); this is the conditional magnetization described above. The field $t\delta_v$ is `fieldAt v t`, and the field $-h-t\delta_v$ appears as `(-h) + fieldAt v (-t)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Influence.lean#L38-L113

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

theorem OAI.BufferedIsing.DSS.influence_step (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g h : V → ℝ) (hh : 0 ≤ h) (v o : V) (t : ℝ) (ht : 0 ≤ t)
    (Hfield : ∀ (g' : V → ℝ) (o' : V),
      mean J (g' + h) o' - mean J (g' - h) o' ≤ mean J h o' - mean J (-h) o')
    (Hpin : pinMean J (g + h) v true o - pinMean J (g - h) v false o ≤
      pinMean J h v true o - pinMean J (-h) v false o) :
    mean J ((g + h) + fieldAt v t) o - mean J ((g - h) + fieldAt v (-t)) o ≤
      mean J (h + fieldAt v t) o - mean J ((-h) + fieldAt v (-t)) o := by sorry
