-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_lintegral_pi_snoc
-- name    : OAI.SubsphereRegression.lintegral_pi_snoc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:11:40.8754+00:00
-- url     : https://prove2.me/theorems/fe7a68b9-b5be-4cec-ba7e-9552728ffd9b
-- title:
--   Tonelli formula integrating out the last coordinate of a finite product measure
-- statement:
--   Let $(E,\mathcal{E})$ be a measurable space, $\nu$ a $\sigma$-finite measure on it and $n\in\mathbb{N}$. Write $\nu^{\otimes k}$ for the product measure on $E^{k}$, and for $v=(v_0,\dots,v_{n-1})\in E^{n}$ and $x\in E$ let $(v,x)=(v_0,\dots,v_{n-1},x)\in E^{n+1}$ be the tuple obtained by appending $x$ as the last coordinate. Then for every measurable function $f:E^{n+1}\to[0,\infty]$,
--   $$\int_{E^{n+1}}f\,d\nu^{\otimes(n+1)}=\int_{E^{n}}\left(\int_{E}f(v,x)\,d\nu(x)\right)d\nu^{\otimes n}(v).$$
--
--   This is Tonelli's theorem in the form needed for induction on the number of independent samples: the last sample is integrated first while the earlier ones are frozen. It is used to bound integrals of products of Gram–Schmidt lengths one sample at a time.
--
--   **Formalization Note** The appended tuple is `Fin.snoc v x`, the product measure is `Measure.pi (fun _ => ν)`, and the integrals are lower Lebesgue integrals `∫⁻` of $[0,\infty]$-valued functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gram.lean#L184-L197

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]

theorem OAI.SubsphereRegression.lintegral_pi_snoc (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => ν) =
      ∫⁻ v : Fin n → E, ∫⁻ x, f (Fin.snoc v x) ∂ν ∂Measure.pi (fun _ => ν) := by sorry
