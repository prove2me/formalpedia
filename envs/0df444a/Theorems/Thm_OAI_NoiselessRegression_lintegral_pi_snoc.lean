-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_lintegral_pi_snoc
-- name    : OAI.NoiselessRegression.lintegral_pi_snoc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:25:27.599239+00:00
-- url     : https://prove2.me/theorems/9c008508-b20b-4f52-b48b-595b91b23243
-- title:
--   Integrating out the last coordinate of a finite product measure
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space, let $\nu$ be a $\sigma$-finite measure on $E$, and let $n\in\mathbb{N}$. Write $\nu^{\otimes k}$ for the product measure on $E^{k}$ (with the product $\sigma$-algebra) and, for $v=(v_0,\dots,v_{n-1})\in E^{n}$ and $x\in E$, write $(v,x)=(v_0,\dots,v_{n-1},x)\in E^{n+1}$. Then for every measurable function $f:E^{n+1}\to[0,\infty]$,
--   $$
--   \int_{E^{n+1}}f\,d\nu^{\otimes(n+1)}=\int_{E^{n}}\left(\int_E f(v,x)\,d\nu(x)\right)d\nu^{\otimes n}(v).
--   $$
--
--   This is Tonelli's theorem in the form needed for induction on the number of independent samples: the last sample is integrated first, with the previous ones held fixed. It is the device by which moments of functions of $n+1$ independent points are bounded through one-step estimates.
--
--   **Formalization Note** The product measure is `Measure.pi (fun _ => ν)` on `Fin (n+1) → E`, the integrals are lower Lebesgue integrals `∫⁻`, and $(v,x)$ is `Fin.snoc v x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Gram.lean#L186-L199

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]

theorem OAI.NoiselessRegression.lintegral_pi_snoc (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => ν) =
      ∫⁻ v : Fin n → E, ∫⁻ x, f (Fin.snoc v x) ∂ν ∂Measure.pi (fun _ => ν) := by sorry
