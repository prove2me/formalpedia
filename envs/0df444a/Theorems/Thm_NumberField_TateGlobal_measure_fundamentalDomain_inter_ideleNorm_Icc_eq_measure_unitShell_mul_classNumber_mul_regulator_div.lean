-- Prove2me | Theorems.Thm_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div
-- name    : NumberField.TateGlobal.measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/bb97cb04-029a-5d69-bc55-88539105065b
-- title:
--   Tate: covolume rate of K^× in the ideles
-- statement:
--   Let $K$ be a number field, and equip the idele group $(\mathbb{A}_K)^\times$ of units of the adele ring with a measurable structure which is the Borel structure of its topology; let $\nu$ be a Haar measure on $(\mathbb{A}_K)^\times$. Write $S$ for the set of ideles $u$ such that, at every height-one prime $v$ of $\mathcal{O}_K$, the finite-adelic component of $u$ at $v$ and the finite-adelic component of $u^{-1}$ at $v$ both lie in the valuation ring $\mathcal{O}_v$ of the completion, and such that, at every infinite place $w$ of $K$, the norm of the infinite-adelic component of $u$ at $w$ lies in $[1,e]$. The assertion is threefold: $\nu(S)\neq 0$; $\nu(S)\neq\infty$; and for every set $\Omega\subseteq(\mathbb{A}_K)^\times$ which is a $\nu$-fundamental domain for the action of the image of $K^\times$ under the map induced by $K\to\mathbb{A}_K$, and all reals $a,b$ with $0<a$ and $a\le b$,
--   $$\nu\bigl(\Omega\cap\{x:\ \|x\|\in[a,b]\}\bigr)=\nu(S)\cdot\frac{h_K\,R_K}{2^{r_2}\,w_K}\cdot\log(b/a),$$
--   where $\|x\|$ is the value at $x$ of the distributive Haar character of $\mathbb{A}_K$ (a nonnegative real), $h_K$ is the class number, $R_K$ the regulator, $r_2$ the number of complex places and $w_K$ the order of the torsion subgroup of $\mathcal{O}_K^\times$; the two real factors are transported to $[0,\infty]$ by `ENNReal.ofReal`.
--
--   This is Tate's evaluation of the volume of the norm-one idele class group $\mathbb{A}_K^1/K^\times$, stated for an arbitrary Haar measure by expressing it relative to the mass of the unit shell $S$, so that no normalisation of the measure need be fixed. It feeds the computation of the growth rate of a Haar measure on a fundamental domain for the global points in [`AutomorphicForm.rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_globalPoints_inter_ideleNorm_det_Icc`](thm.html#AutomorphicForm.rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_globalPoints_inter_ideleNorm_det_Icc).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.TateGlobal.measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} ≠ 0 ∧
    ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} ≠ ⊤ ∧
    ∀ Ω : Set (AdeleRing (𝓞 K) K)ˣ,
      IsFundamentalDomain
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω ν →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        ν (Ω ∩ {x | NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b}) =
          ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} *
            ENNReal.ofReal ((NumberField.classNumber K : ℝ) * NumberField.Units.regulator K /
              (2 ^ NumberField.InfinitePlace.nrComplexPlaces K * (NumberField.Units.torsionOrder K : ℝ))) *
            ENNReal.ofReal (Real.log (b / a)) := by sorry
