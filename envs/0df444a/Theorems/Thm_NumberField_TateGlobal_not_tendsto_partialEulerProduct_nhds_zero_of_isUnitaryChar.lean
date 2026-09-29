-- Prove2me | Theorems.Thm_NumberField_TateGlobal_not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar
-- name    : NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/8ae01be3-0520-5263-ba09-5da4fb3e22f4
-- title:
--   Non-vanishing at s=1 of partial Hecke L-products
-- statement:
--   Let $K$ be a number field and let $\chi \colon (\mathbf{A}_K)^\times \to \mathbb{C}^\times$ be a group homomorphism from the units of the adele ring of $\mathcal{O}_K$ in $K$, subject to three hypotheses: `IsIdeleClassChar`, namely $\chi$ kills the principal ideles, $\chi(\iota(u)) = 1$ for every $u \in K^\times$ with $\iota$ the map induced by $K \to \mathbf{A}_K$; continuity of $\chi$; and `IsUnitaryChar`, namely $\lVert \chi(x) \rVert = 1$ for every idele unit $x$. Let $T$ be a finite set of primes of $\mathcal{O}_K$ (points of the height-one spectrum). For a prime $v$ set $c_v = \chi(\varpi_v)$, where $\varpi_v$ is the idele which is the chosen uniformizer of the completion $K_v$ in the $v$-th coordinate, $1$ at all other finite coordinates and $1$ at the infinite places, provided $\chi$ is unramified at $v$ in the sense that the composite of $\chi$ with the embedding $(K_v)^\times \to (\mathbf{A}_K)^\times$ of the $v$-th local units is trivial on every $t$ with both $t$ and $t^{-1}$ in the valuation ring of $K_v$; and $c_v = 0$ otherwise. The conclusion is that the function $$\sigma \mapsto \prod_{v \notin T} \bigl(1 - c_v \, (\#(\mathcal{O}_K/v))^{-\sigma}\bigr)^{-1},$$ the unconditional `tprod` over the subtype of primes not in $T$, with $\#(\mathcal{O}_K/v)$ the absolute norm of the ideal $v$ and exponent $-\sigma$ taken in $\mathbb{C}$, does not tend to $0$ in $\mathbb{C}$ as the real variable $\sigma$ tends to $1$ from the right, i.e. along the filter $\mathcal{N}[{>}1]$.
--
--   This is the non-vanishing at $s = 1$ of the Hecke $L$-function of a unitary idele class character of $K$ with the Euler factors at $T$ and at the ramified places removed, in the limiting form appropriate for Tate's global theory; by the usual twisting argument it encodes non-vanishing on the whole line $\operatorname{Re} s = 1$. It feeds the converse-theorem and cuspidality steps in the Langlands–Tunnell part of the development, and the construction of an analytic inverse of the partial Euler product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical in

theorem NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hχ : IsIdeleClassChar (𝓞 K) K χ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 K) K χ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ¬ Filter.Tendsto
        (fun σ : ℝ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹)
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (0 : ℂ)) := by sorry
