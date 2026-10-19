-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_coeff_finite_sum
-- name    : OAI.AsymptoticallyMinimalLittlewood.Auxiliary.coeff_finite_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:55:15.493984+00:00
-- url     : https://prove2.me/theorems/1aa7b4d0-38fc-4500-91dd-188a4119ec11
-- title:
--   Fourier coefficients of a trigonometric polynomial on the torus $\mathbb{T}^{n}$ are its coefficients
-- statement:
--   Let $n\ge 0$ and let $\mathbb{T}^{n}=(\mathbb{R}/\mathbb{Z})^{n}$ carry its Haar probability measure $dx$ (Lebesgue measure on $[0,1)^{n}$). For $s\in\mathbb{Z}^{n}$ let $e_s(x)=\exp\bigl(2\pi i\sum_{i}s_ix_i\bigr)$ be the corresponding character (well defined on $\mathbb{T}^{n}$ because the $s_i$ are integers), and for $f:\mathbb{T}^{n}\to\mathbb{C}$ let
--   $$
--   \hat f(s)=\int_{\mathbb{T}^{n}}e_{-s}(x)\,f(x)\,dx=\int_{\mathbb{T}^{n}}\overline{e_s(x)}\,f(x)\,dx
--   $$
--   be its Fourier coefficient at $s$. Let $c:\mathbb{Z}^{n}\to\mathbb{C}$ be finitely supported, with support $S=\{t: c_t\ne 0\}$, and let $f(x)=\sum_{t\in S}c_t\,e_t(x)$. Then for every $s\in\mathbb{Z}^{n}$,
--
--   $$
--   \hat f(s)=c_s .
--   $$
--
--   In particular $\hat f(s)=0$ for $s\notin S$. This expresses the uniqueness of the coefficients of a trigonometric polynomial on the torus; combined with Parseval's identity it identifies the $\ell^{2}$ norm of the coefficient family with the $L^{2}$ norm of $f$.
--
--   **Formalization Note** The character $e_s$ is `UnitAddTorus.mFourier s` and $\hat f(s)$ is `UnitAddTorus.mFourierCoeff f s` (both from Mathlib, with the normalized Haar measure on `UnitAddCircle`); the finitely supported family is a `Finsupp` `(Fin n → ℤ) →₀ ℂ` and $S$ is its `support`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/BinaryPacket.lean#L391-L409

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Auxiliary
universe uE uX
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
open UnitAddTorus
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI

theorem OAI.AsymptoticallyMinimalLittlewood.Auxiliary.coeff_finite_sum {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (s : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ ∑ t ∈ c.support, c t*mFourier t x) s = c s := by sorry
