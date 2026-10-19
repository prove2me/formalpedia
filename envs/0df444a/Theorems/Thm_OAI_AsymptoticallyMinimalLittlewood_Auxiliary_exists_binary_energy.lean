-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_exists_binary_energy
-- name    : OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_binary_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:54:37.062289+00:00
-- url     : https://prove2.me/theorems/146040f5-dbe7-4d6a-988c-63fb8f91e5ad
-- title:
--   The energies of the binary cosine recursion approach $1$: some $E_d\ge 1-\delta$ with $d\ge 2$
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$. Define functions $B_n:\mathbb{T}^{n}\to\mathbb{R}$ recursively by $B_0=0$ and
--   $$
--   B_{n+1}(x_0,x_1,\dots,x_n)=B_n(x_1,\dots,x_n)+\frac{1-B_n(x_1,\dots,x_n)^{2}}{2}\,\cos(2\pi x_0).
--   $$
--
--   Equip $\mathbb{T}$ with its Haar probability measure (Lebesgue measure on $[0,1)$) and $\mathbb{T}^{n}$ with the product measure $dx$, and let $E_n=\int_{\mathbb{T}^{n}}B_n(x)^{2}\,dx$ be the energy of $B_n$. Then for every $\delta>0$ there is an integer $d\ge 2$ with
--
--   $$
--   E_d\ge 1-\delta .
--   $$
--
--   Since $E_n$ is also nondecreasing in $n$ and bounded above by $1$, this means that $E_n\to 1$. In the construction of flat Littlewood polynomials it supplies a depth $d$ at which the trigonometric polynomial $B_d$, which takes values in $[-1,1]$, carries $L^{2}$ mass at least $1-\delta$.
--
--   **Formalization Note** The circle $\mathbb{T}$ is `UnitAddCircle`, given the Haar probability measure by local instances, and $\mathbb{T}^{n}$ is `Fin n → UnitAddCircle` with the product measure. $B_n$ is `binary n`, $E_n$ is `energy n`, and $\cos(2\pi x)$ is `cosine x`, defined as the real part of `fourier 1 x`; in the recursion $x_0$ is `x 0` and $(x_1,\dots,x_n)$ is `Fin.tail x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/BinaryPacket.lean#L196-L219

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

theorem OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_binary_energy {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : ℕ, 2 ≤ d ∧ 1-δ ≤ energy d := by sorry
