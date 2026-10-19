-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_energy_increment
-- name    : OAI.AsymptoticallyMinimalLittlewood.Auxiliary.energy_increment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:53:49.939455+00:00
-- url     : https://prove2.me/theorems/59ea24f7-e68f-4129-a601-e1c5ce5925ba
-- title:
--   Energy increment for the binary cosine recursion: $E_{n+1}\ge E_n+(1-E_n)^{2}/8$
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$. Define functions $B_n:\mathbb{T}^{n}\to\mathbb{R}$ recursively by $B_0=0$ and
--   $$
--   B_{n+1}(x_0,x_1,\dots,x_n)=B_n(x_1,\dots,x_n)+\frac{1-B_n(x_1,\dots,x_n)^{2}}{2}\,\cos(2\pi x_0).
--   $$
--
--   Equip $\mathbb{T}$ with its Haar probability measure (Lebesgue measure on $[0,1)$) and $\mathbb{T}^{n}$ with the product measure $dx$, and let $E_n=\int_{\mathbb{T}^{n}}B_n(x)^{2}\,dx$ be the energy of $B_n$. Then for every $n\ge 0$,
--
--   $$
--   E_n+\frac{(1-E_n)^{2}}{8}\le E_{n+1}.
--   $$
--
--   Thus the energy increases by a definite amount as long as it is bounded away from $1$. Together with $E_n\le 1$ this forces $E_n\to 1$, so that $B_n$ for large $n$ is a trigonometric polynomial with values in $[-1,1]$ and $L^{2}$ norm close to $1$.
--
--   **Formalization Note** The circle $\mathbb{T}$ is `UnitAddCircle`, given the Haar probability measure by local instances, and $\mathbb{T}^{n}$ is `Fin n → UnitAddCircle` with the product measure. $B_n$ is `binary n`, $E_n$ is `energy n`, and $\cos(2\pi x)$ is `cosine x`, defined as the real part of `fourier 1 x`; in the recursion $x_0$ is `x 0` and $(x_1,\dots,x_n)$ is `Fin.tail x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/BinaryPacket.lean#L177-L189

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Auxiliary
universe uE uX
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI

theorem OAI.AsymptoticallyMinimalLittlewood.Auxiliary.energy_increment (n : ℕ) : energy n+(1-energy n)^2/8 ≤ energy (n+1) := by sorry
