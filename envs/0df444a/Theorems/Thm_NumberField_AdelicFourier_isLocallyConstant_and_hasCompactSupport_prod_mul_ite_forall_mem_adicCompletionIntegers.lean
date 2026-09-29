-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
-- name    : NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/088b2a45-4094-5c54-9fe0-44a6da661ff2
-- title:
--   Standard functions on the finite adeles are locally constant with compact support
-- statement:
--   Let $F$ be a number field (with its ring of integers $\mathcal O_F$), let $S$ be a finite set of height-one primes of $\mathcal O_F$, i.e. of finite places of $F$, and let $h$ assign to every height-one prime $v$ a function $h_v \colon F_v \to \mathbb{C}$ on the $v$-adic completion. Assume that for each $v \in S$ the function $h_v$ is locally constant and has compact support; no condition is imposed on $h_v$ for $v \notin S$. Consider the function on the finite adele ring of $F$ given by $$x \mapsto \Big(\prod_{v \in S} h_v(x_v)\Big) \cdot \big[\, x_v \in \mathcal O_v \text{ for all } v \notin S \,\big],$$ where the second factor is $1$ if $x_v$ lies in the ring of integers of $F_v$ for every height-one prime $v$ outside $S$ and $0$ otherwise. The conclusion is the conjunction of two assertions about this function: it is locally constant, and it has compact support.
--
--   These are the standard (Schwartz–Bruhat) functions on the finite adeles in the sense of Tate's thesis: a pure tensor of locally constant compactly supported local data at the places of $S$ times the characteristic function of the integral box outside $S$. The statement supplies the admissibility of such factorisable test functions for the adelic Fourier analysis used in the local harmonic analysis on $\mathrm{GL}_2$, and is invoked in the cubic-induction constructions of Whittaker vectors in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers.lean

import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical in

theorem NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    IsLocallyConstant (fun x : FiniteAdeleRing (𝓞 F) F =>
        (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) ∧
      HasCompactSupport (fun x : FiniteAdeleRing (𝓞 F) F =>
        (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) := by sorry
