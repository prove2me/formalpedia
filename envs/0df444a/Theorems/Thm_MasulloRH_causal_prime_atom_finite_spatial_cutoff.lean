-- Prove2me | Theorems.Thm_MasulloRH_causal_prime_atom_finite_spatial_cutoff
-- name    : MasulloRH.causal_prime_atom_finite_spatial_cutoff
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T19:46:55.211671+00:00
-- url     : https://prove2.me/theorems/1cf19c76-703d-4111-bb8a-33c56a6910ac
-- title:
--   Finite spatial cutoffs strictly attenuate each positive-lag atom of the causal prime projection model
-- statement:
--   Let $L>0$, $0<r<1$, $a_0=-r$ and $a_{i+1}=(1-r^2)r^i$. These are the delayed atom amplitudes of $(z-r)/(1-rz)$ at $z=e^{-Ls}$. For integer lag $k\ge1$ and real endpoint $R$, the signed atom-pair contribution is
--   $$C_k(R)=-\sum_{i\ge0}a_i a_{i+k}(R-(i+k)L)_+.$$
--   It vanishes up to $R=kL$. At $R=(k+m)L+\theta$, with $m\ge0$ and $0\le\theta\le L$, it equals the negative integral on $[0,R]$ of the causal step function $\sum_{i=0}^m a_i a_{i+k}\mathbf1_{x>(i+k)L}$. Both the finite overlap sum and this integral equal
--   $$r^k\big[L(1-r^{2m})+(1-r^2)r^{2m}\theta\big].$$
--   The normalized deficit $L-C_k(R)/r^k$ lies between $Lr^{2m+2}$ and $Lr^{2m}$. Every finite real endpoint satisfies $C_k(R)<Lr^k$, and $C_k(R)\to Lr^k$ along the full real cutoff. If $r=e^{-\alpha L}$ and $\alpha+b=1/2$, the rescaled coefficient $e^{-bkL}C_k(R)$ stays strictly below $Le^{-kL/2}$ and tends to it. For $L=\log p$ this limiting value is $(\log p)p^{-k/2}$.
-- source:
--   Masullo, The Music of the Primes, frozen 20 November 2026, §§7.3.2, 11.3.2 (especially equation 11.3.2.4), and 12.4. New direct calculation for the finite-cutoff pure atom-pair part of the causal prime projection model. The atom-pair length is the positive part of R minus (i+k)L. The adjacent log-cell reference-pole overlap 9f8d3d6f-1c98-4e15-8ab8-eee4e526ae48 is a distinct rank-one calculation. Identification of the present model with a compact-window limit of global Hilbert-space projections is separate from the formal result.

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open Finset Filter MeasureTheory Set
open scoped BigOperators Topology

theorem MasulloRH.causal_prime_atom_finite_spatial_cutoff (r L : ℝ) (hr : 0 < r) (hr' : r < 1) (hL : 0 < L)
    (a : ℕ → ℝ) (ha0 : a 0 = -r) (ha : ∀ i, a (i+1) = (1-r^2)*r^i)
    (k : ℕ) (hk : 1 ≤ k) :
    let C := fun R : ℝ => -(∑' i : ℕ, a i*a (i+k) * max (R-((i:ℝ)+(k:ℝ))*L) 0)
    let tau := fun (m : ℕ) (θ : ℝ) => ((k:ℝ)+(m:ℝ))*L+θ
    (∀ R, R ≤ (k:ℝ)*L → C R = 0) ∧
    (∀ (m : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ L →
      (-(∫ x in (0:ℝ)..tau m θ, ∑ i ∈ Finset.range (m+1),
        if ((i:ℝ)+(k:ℝ))*L < x then a i*a (i+k) else 0)) = C (tau m θ) ∧
      C (tau m θ) = -(∑ i ∈ Finset.range (m+1), a i*a (i+k) * (tau m θ-((i:ℝ)+(k:ℝ))*L)) ∧
      C (tau m θ) = r^k*(L*(1-(r^2)^m)+(1-r^2)*(r^2)^m*θ) ∧
      L*(r^2)^(m+1) ≤ L - C (tau m θ)/r^k ∧ L - C (tau m θ)/r^k ≤ L*(r^2)^m) ∧
    (∀ R, C R < L*r^k) ∧ Tendsto C atTop (𝓝 (L*r^k)) ∧
    (∀ b α : ℝ, α+b = 1/2 → r = Real.exp (-α*L) →
      let z := Real.exp (-b*(k:ℝ)*L)
      (∀ R, z*C R < L*Real.exp (-((k:ℝ)*L)/2)) ∧
      Tendsto (fun R => z*C R) atTop (𝓝 (L*Real.exp (-((k:ℝ)*L)/2)))) := by sorry
