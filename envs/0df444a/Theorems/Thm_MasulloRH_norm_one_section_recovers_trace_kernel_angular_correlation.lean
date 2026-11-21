-- Prove2me | Theorems.Thm_MasulloRH_norm_one_section_recovers_trace_kernel_angular_correlation
-- name    : MasulloRH.norm_one_section_recovers_trace_kernel_angular_correlation
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:03:03.254191+00:00
-- url     : https://prove2.me/theorems/9fde95a4-6ef5-4502-b4fe-a5a14524f969
-- title:
--   The norm-one section recovers the angular correlation with an integrable trace bound
-- statement:
--   Let $G=A\times H$ be a second-countable locally compact abelian group, with product Haar measure $\mu=dt\,dh$ where $H$ has Haar probability measure. Suppose a kernel $K(z,w)=\langle a(z),b(w)\rangle$ holds product-almost everywhere for locally Bochner integrable square-integrable Hilbert features $a,b$. Assume $K(hz,hw)=K(z,w)$ product-almost everywhere for each $h\in H$ acting in the second coordinate. For almost every $t$, **every** $g\in H$, and every continuous complex multiplier $q$, the normalized rectangular averages of $qK$ for any Haar $D'$ basis at $((t,1),(t,g))$ tend as the two radii shrink independently to $q((t,1),(t,g))L_t(g)$, where
--   $$L_t(g)=\int_H\langle a(t,h),b(t,gh)\rangle\,dh.$$
--   The bound $|L_t(g)|\le B(t)$ holds simultaneously in $g$, where $B(t)=\tfrac12\int_H(\|a(t,h)\|^2+\|b(t,h)\|^2)\,dh$ is integrable and $\int_A B(t)\,dt=(\|a\|_2^2+\|b\|_2^2)/2$. For balanced Schmidt factors the latter is the trace norm. This identifies the regularized value on an often Haar-null section.
-- source:
--   Masullo, The Music of the Primes, frozen 20 November 2026, (10.4.1.1–3), Remark 10.4.1.4, (10.4.3.43–47), and (11.3.2.1–3). Continues the proved fixed-kernel recovery e2bdca15-5ce0-421b-8bd1-931f915590df, earlier multiplier estimate cbb83452-e074-466f-aa6a-99fb9a9b4110 and discussion 90bc8361-7f41-4c90-aba8-fd214c4b2c35. The rational normalized shell-mass question comes from comment 65e3e214. The theorem assumes simultaneous norm-one equivariance; it imposes no radial group-equivariance, independence of group and radial variables, or product shape for the differentiation basis.

import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Metrizable.Urysohn
import Definitions.Def_MasulloGRH_DSequences
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set MeasureTheory Filter
open scoped Pointwise ENNReal
open MasulloGRH
open scoped Topology

theorem MasulloRH.norm_one_section_recovers_trace_kernel_angular_correlation
    {A H : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (μA : Measure A) [μA.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [IsProbabilityMeasure ν]
    (U : ℕ → Set (A × H)) (C : ℝ) (hU : IsDPrimeSequence (μA.prod ν) U C)
    (a b : A × H → E) (ha : LocallyIntegrable a (μA.prod ν)) (hb : LocallyIntegrable b (μA.prod ν))
    (K : (A × H) × (A × H) → ℂ) (hK : K =ᵐ[(μA.prod ν).prod (μA.prod ν)]
      (fun z => inner ℂ (a z.1) (b z.2)))
    (hinv : ∀ h : H, (fun z : (A × H) × (A × H) => K ((1,h)*z.1,(1,h)*z.2))
      =ᵐ[(μA.prod ν).prod (μA.prod ν)] K)
    (ha2 : Integrable (fun z => ‖a z‖^2) (μA.prod ν))
    (hb2 : Integrable (fun z => ‖b z‖^2) (μA.prod ν)) :
    let L := fun t g => ∫ h, inner ℂ (a (t,h)) (b (t,g*h)) ∂ν
    let B := fun t => ((∫ h, ‖a (t,h)‖^2 ∂ν) + (∫ h, ‖b (t,h)‖^2 ∂ν)) / 2
    Integrable B μA ∧
    (∫ t, B t ∂μA) = ((∫ z, ‖a z‖^2 ∂μA.prod ν) + (∫ z, ‖b z‖^2 ∂μA.prod ν)) / 2 ∧
    ∀ᵐ t ∂μA, ∀ g : H, ‖L t g‖ ≤ B t ∧ ∀ (q : (A × H) × (A × H) → ℂ), Continuous q →
      Tendsto (fun kl : ℕ × ℕ =>
        ((((μA.prod ν) (U kl.1)).toReal)⁻¹ * (((μA.prod ν) (U kl.2)).toReal)⁻¹) •
          ∫ z in ((t,(1:H)) • U kl.1) ×ˢ ((t,g) • U kl.2),
            q z * K z ∂(μA.prod ν).prod (μA.prod ν))
      atTop (𝓝 (q ((t,1),(t,g)) * L t g)) := by sorry
