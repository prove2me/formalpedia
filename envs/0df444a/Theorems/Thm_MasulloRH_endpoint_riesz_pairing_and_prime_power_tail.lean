-- Prove2me | Theorems.Thm_MasulloRH_endpoint_riesz_pairing_and_prime_power_tail
-- name    : MasulloRH.endpoint_riesz_pairing_and_prime_power_tail
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:29:20.196784+00:00
-- url     : https://prove2.me/theorems/b674a7b3-7137-4fcc-ab72-f980024abb74
-- title:
--   Endpoint Riesz vector on the logarithmic line and its prime-power dilation tail
-- statement:
--   On the real logarithmic line take the weight $w(u)=e^{|u|}(1+u^2)$ and the Riesz vector $k(u)=e^{u/2}/w(u)$. Let $Z=\int_{\mathbb R}e^{u-|u|}(1+u^2)^{-1}\,du$. The normalization $Z$ is finite and strictly positive. For every real displacement $b$, the weighted pairing is absolutely integrable and
--   $$\int_{\mathbb R} k(u-b)k(u)w(u)\,du =e^{b/2}Z.$$
--   For every real base $p>1$ and $s\in\mathbb R$, summing these integrals at $b=s-j\log p$, $j=1,2,\ldots$, gives $e^{s/2}Z/(\sqrt p-1)$. After restricting the integral to any spatial set, the tail starting at $j=J+1$ is still absolutely summable and is at most $p^{-J/2}e^{s/2}Z/(\sqrt p-1)$, uniformly in the set.
-- source:
--   Endpoint-weighted rank-one evaluation in the rational logarithmic chart of the Masullo RH mission. This calculation addresses the ambient weighted Riesz vector and its prime-power dilation pairing.

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Positivity

open MeasureTheory

theorem MasulloRH.endpoint_riesz_pairing_and_prime_power_tail :
    let w (u : ℝ) := Real.exp |u| * (1 + u^2)
    let k (u : ℝ) := Real.exp (u/2) / w u
    let h (u : ℝ) := Real.exp (u - |u|) / (1 + u^2)
    let z := ∫ u : ℝ, h u
    let a (b u : ℝ) := k (u-b)*k u*w u
    Integrable h ∧ 0 < z ∧
    (∀ b : ℝ, Integrable (a b) ∧ (∫ u : ℝ, a b u) = Real.exp (b/2)*z) ∧
    (∀ p s : ℝ, 1<p →
      HasSum (fun j : ℕ => ∫ u : ℝ, a (s-((j:ℝ)+1)*Real.log p) u)
        (Real.exp (s/2)*z/(Real.sqrt p-1)) ∧
      ∀ (V : Set ℝ) (J : ℕ),
        let t (j : ℕ) := ∫ u in V, a ((s-(J:ℝ)*Real.log p)-((j:ℝ)+1)*Real.log p) u
        Summable t ∧ (∑' j : ℕ, t j) ≤ Real.exp ((s-(J:ℝ)*Real.log p)/2)*z/(Real.sqrt p-1)) := by sorry
