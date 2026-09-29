-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
-- name    : NumberField.TateGlobal.exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/1e6b77e6-7df6-5872-af91-3b7661c69aa1
-- title:
--   Entire partial Euler product for a non-trivial idele class character
-- statement:
--   Let $K$ be a number field and let $\chi \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be a group homomorphism on the units of the adele ring of $\mathcal{O}_K$ in $K$ subject to four conditions: `IsIdeleClassChar`, i.e. $\chi$ kills the principal ideles, $\chi(\iota(u)) = 1$ for every $u \in K^\times$ with $\iota$ the map induced by $K \to \mathbb{A}_K$; continuity of $\chi$; `IsUnitaryChar`, i.e. $\lVert \chi(x) \rVert = 1$ for every idele $x$; and the existence of some $x$ in `normOneIdeles K`, the kernel of the distributive Haar character of the adele ring, with $\chi(x) \neq 1$. Let $T$ be a finite set of primes of $\mathcal{O}_K$ (points of the height-one spectrum). Then there is a function $L \colon \mathbb{C} \to \mathbb{C}$, differentiable on all of $\mathbb{C}$, such that for every $s$ with $\operatorname{Re} s > 1$ one has $$L(s) = \prod_{v \notin T}{}' \bigl(1 - c_v \,(\mathrm{N}v)^{-s}\bigr)^{-1},$$ the unconditional product (`tprod`) over the primes $v$ of $\mathcal{O}_K$ outside $T$, where $\mathrm{N}v$ is the absolute norm of the ideal $v$, and where $c_v = \chi(\mathrm{uniformizerIdele}\,v)$ — the value of $\chi$ on the idele which is a uniformizer of $K_v$ at $v$ and $1$ at every other place — if `IsUnramifiedCharAt χ v` holds, that is if the local component of $\chi$ at $v$ is trivial on every unit of $K_v$ whose inverse also lies in the valuation ring, and $c_v = 0$ otherwise.
--
--   This is the pole-free half of the main theorem of Tate's thesis, in partial-Euler-product form: for a unitary idele class character that is non-trivial on the norm-one ideles the Hecke $L$-function, with the Euler factors at the places of $T$ and at the ramified places removed, extends to an entire function. It is invoked in the construction of entire twisted $L$-functions and in the continuation and growth estimates for intertwining integrals attached to induced sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one.lean

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm
open scoped Classical in

theorem NumberField.TateGlobal.exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ) (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 K) K χ)
    (hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by sorry
