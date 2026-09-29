-- Prove2me | Theorems.Thm_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div
-- name    : NumberField.TateGlobal.measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/216f3312-5348-51ae-9b84-b4963f942a47
-- title:
--   Regulator term for unit idele classes of bounded norm
-- statement:
--   Let $K$ be a number field, and equip the idele group $(\mathbb{A}_K)^\times =$ `(AdeleRing (𝓞 K) K)ˣ` with a measurable structure which is the Borel structure of its topology; let $\nu$ be a measure on it which is assumed to be a Haar measure. Write $\mathrm{Sh}$ for the set of ideles $u$ such that at every finite place $v$ (i.e. every height-one prime $v$ of $\mathcal{O}_K$) both the $v$-component of the finite part of $u$ and the $v$-component of the finite part of $u^{-1}$ lie in the valuation ring $\mathcal{O}_v$, and such that $\|u_w\| \in [1, e]$ at every infinite place $w$ of $K$, the infinite components being read off from the infinite part of $u$; and write $U =$ `unitIdelesOutside (𝓞 K) K ∅` for the subgroup of ideles satisfying the first of these two conditions alone, i.e. those that are units at every finite place. The assertion is threefold: $\nu(\mathrm{Sh}) \neq 0$; $\nu(\mathrm{Sh}) \neq \infty$; and, for every set $F$ of ideles that is a fundamental domain, with respect to the restriction of $\nu$ to $U$, for the action of the subgroup obtained by intersecting $U$ with the image of $K^\times$ under the map induced on units by $K \to \mathbb{A}_K$, and for all reals $a, b$ with $0 < a \le b$,
--   $$\nu\bigl(U \cap F \cap \{x : \|x\| \in [a,b]\}\bigr) = \nu(\mathrm{Sh}) \cdot \frac{R_K}{2^{r_2} w_K} \cdot \log(b/a),$$
--   where $\|x\| =$ `ideleNorm K x` is the module of $x$, namely the distributive Haar character of the multiplication action of $x$ on $\mathbb{A}_K$, $R_K$ is the regulator of $K$, $r_2$ the number of complex places and $w_K$ the order of the torsion subgroup of $\mathcal{O}_K^\times$; the two real factors on the right are coerced to $[0,\infty]$.
--
--   This is the regulator contribution to Tate's computation of the volume of the norm-one idele class group, isolated here for an arbitrary Haar measure on $(\mathbb{A}_K)^\times$ by expressing the answer relative to the mass of the unit shell $\mathrm{Sh}$, so that no normalisation of $\nu$ need be fixed. It feeds into the corresponding statement for a fundamental domain of the full principal idele group, where the class number appears as an extra factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.TateGlobal.measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div
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
    ∀ F : Set (AdeleRing (𝓞 K) K)ˣ,
      IsFundamentalDomain
        ↥((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ⊓
          NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K)))) F
        (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))))) →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        ν ((NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))) :
              Set (AdeleRing (𝓞 K) K)ˣ) ∩ F ∩
            {x | NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b}) =
          ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} *
            ENNReal.ofReal (NumberField.Units.regulator K /
              (2 ^ NumberField.InfinitePlace.nrComplexPlaces K * (NumberField.Units.torsionOrder K : ℝ))) *
            ENNReal.ofReal (Real.log (b / a)) := by sorry
