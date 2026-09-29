-- Prove2me | Theorems.Thm_NumberField_Idele_exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty
-- name    : NumberField.Idele.exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/5663d139-dd70-5274-924f-bac251a77bbc
-- title:
--   A ball indicator at S integrates out of the S-part measure
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}_K$, let $S$ be a finite set of height-one primes of $\mathcal{O}_K$, let $t_0$ be a unit of the adele ring $\mathbb{A}_K$ whose finite component satisfies $t_{0,v}=1$ for every $v\notin S$, and let $nb$ be a natural number with $nb>0$; the idele group $\mathbb{A}_K^{\times}$ carries the Borel $\sigma$-algebra of its topology. Write $\nu_S$ for the measure `sPartMeasure K S`, i.e. the pushforward under `partAt K S` (the unit-group map induced by $a\mapsto(a_\infty,\ \mathrm{truncFin}\,S\,a_{\mathrm{fin}})$) of the Haar measure `idelicHaar K` restricted to the subgroup of ideles $\delta$ with $\delta_v$ and $(\delta^{-1})_v$ both $v$-integral for all $v\notin S$, and similarly $\nu_\varnothing$ for $S=\varnothing$. Then there exists a real $\kappa>0$ such that, with $B$ the set of ideles $t$ satisfying $v(t_v-t_{0,v})\le v(t_{0,v})\cdot q_v^{-nb}$ (valuations in $\mathbb{Z}^{\mathrm{mult}}_{\ge 0}$, the bound written via $\mathrm{ofAdd}(-nb)$) for all $v\in S$: first, for every measurable $f:\mathbb{A}_K^{\times}\to[0,\infty]$ one has $\int^{-} \mathbf 1_B(t)\,f(\mathrm{partAt}\,K\,\varnothing\,t)\,d\nu_S = \mathrm{ofReal}(\kappa)\int^{-} f\,d\nu_\varnothing$; and second, for every $f:\mathbb{A}_K^{\times}\to\mathbb{C}$ integrable for $\nu_\varnothing$, the function $t\mapsto \mathbf 1_B(t) f(\mathrm{partAt}\,K\,\varnothing\,t)$ is integrable for $\nu_S$ and its integral equals $\kappa\int f\,d\nu_\varnothing$.
--
--   This is the local computation at the places of $S$ which lets a test function supported in a small ball around a fixed torus point be integrated against the $S$-part idele measure, the ball contributing only a positive volume factor $\kappa$ independent of $f$; both a nonnegative (lower-integral) and a complex (Bochner) form are asserted. It is used in the Rankin–Selberg part of the argument, by [`AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery`](thm.html#AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery), to replace integrals over a torus pair by integrals over the archimedean torus alone.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
    (nb : ℕ) (_hnb : 0 < nb) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable f →
        (∫⁻ t, (if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then f (NumberField.Idele.partAt K ∅ t) else 0)
            ∂(NumberField.Idele.sPartMeasure K S)) =
          ENNReal.ofReal κ * ∫⁻ t, f t ∂(NumberField.Idele.sPartMeasure K ∅)) ∧
      (∀ f : (AdeleRing (𝓞 K) K)ˣ → ℂ, Integrable f (NumberField.Idele.sPartMeasure K ∅) →
        Integrable (fun t : (AdeleRing (𝓞 K) K)ˣ => if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then f (NumberField.Idele.partAt K ∅ t) else 0)
            (NumberField.Idele.sPartMeasure K S) ∧
        (∫ t, (if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then f (NumberField.Idele.partAt K ∅ t) else 0)
            ∂(NumberField.Idele.sPartMeasure K S)) =
          (κ : ℂ) * ∫ t, f t ∂(NumberField.Idele.sPartMeasure K ∅)) := by sorry
