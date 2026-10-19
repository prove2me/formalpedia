-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_binary_coefficients_energy
-- name    : OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_coefficients_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:55:51.034836+00:00
-- url     : https://prove2.me/theorems/dcba5c1f-6dc7-4707-a22d-b3bf2fcbcae0
-- title:
--   Parseval identity for the binary cosine recursion: the squared Fourier coefficients of $B_n$ sum to its energy
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$. Define functions $B_n:\mathbb{T}^{n}\to\mathbb{R}$ recursively by $B_0=0$ and
--   $$
--   B_{n+1}(x_0,x_1,\dots,x_n)=B_n(x_1,\dots,x_n)+\frac{1-B_n(x_1,\dots,x_n)^{2}}{2}\,\cos(2\pi x_0).
--   $$
--
--   Equip $\mathbb{T}$ with its Haar probability measure (Lebesgue measure on $[0,1)$) and $\mathbb{T}^{n}$ with the product measure $dx$, and let $E_n=\int_{\mathbb{T}^{n}}B_n(x)^{2}\,dx$ be the energy of $B_n$. For $s\in\mathbb{Z}^{n}$ let $e_s(x)=\exp\bigl(2\pi i\sum_{i}s_ix_i\bigr)$ be the corresponding character (well defined on $\mathbb{T}^{n}$ because the $s_i$ are integers), and for $f:\mathbb{T}^{n}\to\mathbb{C}$ let
--   $$
--   \hat f(s)=\int_{\mathbb{T}^{n}}e_{-s}(x)\,f(x)\,dx=\int_{\mathbb{T}^{n}}\overline{e_s(x)}\,f(x)\,dx
--   $$
--   be its Fourier coefficient at $s$. Let $c:\mathbb{Z}^{n}\to\mathbb{C}$ be finitely supported with support $S=\{s: c_s\ne 0\}$, and suppose that
--   $$
--   B_n(x)=\sum_{s\in S}c_s\,e_s(x)\qquad\text{for all }x\in\mathbb{T}^{n}.
--   $$
--   Then
--
--   $$
--   \sum_{s\in S}|c_s|^{2}=E_n .
--   $$
--
--   So the energy of $B_n$ equals the $\ell^{2}$ norm squared of its coefficient family. In the construction of flat Littlewood polynomials the coefficients $c_s$ serve as amplitudes, and this identity, together with $E_n\ge 1-\delta$ for suitable $n$, shows that their total squared size is close to $1$.
--
--   **Formalization Note** The circle $\mathbb{T}$ is `UnitAddCircle`, given the Haar probability measure by local instances, and $\mathbb{T}^{n}$ is `Fin n → UnitAddCircle` with the product measure. $B_n$ is `binary n`, $E_n$ is `energy n`, and $\cos(2\pi x)$ is `cosine x`, defined as the real part of `fourier 1 x`; in the recursion $x_0$ is `x 0` and $(x_1,\dots,x_n)$ is `Fin.tail x`. The character $e_s$ is `UnitAddTorus.mFourier s` and $\hat f(s)$ is `UnitAddTorus.mFourierCoeff f s` (both from Mathlib, with the normalized Haar measure on `UnitAddCircle`); the finitely supported family is a `Finsupp` `(Fin n → ℤ) →₀ ℂ` and $S$ is its `support`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/BinaryPacket.lean#L429-L447

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

theorem OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_coefficients_energy {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) :
    (∑ s ∈ c.support, ‖c s‖^2) = energy n := by sorry
