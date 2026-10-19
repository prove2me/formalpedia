-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_binary_abs_le
-- name    : OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_abs_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:53:06.250257+00:00
-- url     : https://prove2.me/theorems/84c8ef52-8fb2-4c34-9fe8-2dfff6a8303b
-- title:
--   The binary cosine recursion $B_{n+1}=B_n+\tfrac12(1-B_n^{2})\cos(2\pi x_0)$ stays in $[-1,1]$
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$. Define functions $B_n:\mathbb{T}^{n}\to\mathbb{R}$ recursively by $B_0=0$ and
--   $$
--   B_{n+1}(x_0,x_1,\dots,x_n)=B_n(x_1,\dots,x_n)+\frac{1-B_n(x_1,\dots,x_n)^{2}}{2}\,\cos(2\pi x_0).
--   $$ Then for every $n\ge 0$ and every $x\in\mathbb{T}^{n}$,
--
--   $$
--   |B_n(x)|\le 1 .
--   $$
--
--   Each $B_n$ is a real trigonometric polynomial in $n$ variables. At every step a new cosine is added with amplitude $\tfrac12(1-B_n^{2})$, which is large where $B_n$ is far from $\pm1$ and vanishes where $|B_n|=1$; the theorem says that this never pushes the values outside $[-1,1]$. It gives the energy bound $\int_{\mathbb{T}^{n}}B_n^{2}\le 1$ for the Haar probability measure and controls the size of the functions built from $B_n$ in the construction of flat polynomials.
--
--   **Formalization Note** The circle $\mathbb{T}$ is `UnitAddCircle`, given the Haar probability measure by local instances, and $\mathbb{T}^{n}$ is `Fin n → UnitAddCircle` with the product measure. $B_n$ is `binary n`, $E_n$ is `energy n`, and $\cos(2\pi x)$ is `cosine x`, defined as the real part of `fourier 1 x`; in the recursion $x_0$ is `x 0` and $(x_1,\dots,x_n)$ is `Fin.tail x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/BinaryPacket.lean#L100-L114

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

theorem OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_abs_le (n : ℕ) (x : Fin n → UnitAddCircle) : |binary n x| ≤ 1 := by sorry
