-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_latticeWeight_summable
-- name    : OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.latticeWeight_summable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:03:46.544985+00:00
-- url     : https://prove2.me/theorems/0f42421a-e717-4922-a7b8-718c11491904
-- title:
--   The lattice weight $(1+|w|)^{-2}$ is summable over the integers
-- statement:
--   For an integer $w$ define the lattice weight $\lambda(w)=\dfrac{1}{(1+|w|)^2}$. Then the family $(\lambda(w))_{w\in\mathbb{Z}}$ is summable, that is,
--
--   $$
--   \sum_{w\in\mathbb{Z}}\frac{1}{(1+|w|)^2}<\infty .
--   $$
--
--   The weight $\lambda$ serves as a summable majorant on the lattice $\mathbb{Z}$ of Fourier frequencies: once the Fourier coefficients of a function are shown to be at most a constant times $\lambda(w)$ outside a finite window, the discarded part of the Fourier series is bounded, uniformly on the circle, by that constant times $\sum_{w}\lambda(w)$.
--
--   **Formalization Note** The weight is `latticeWeight`; summability is Mathlib's `Summable` (unconditional summability of a family indexed by the integers), which for nonnegative terms is the same as finiteness of the sum.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean#L322-L333

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
universe uI uZ
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.latticeWeight_summable : Summable latticeWeight := by sorry
