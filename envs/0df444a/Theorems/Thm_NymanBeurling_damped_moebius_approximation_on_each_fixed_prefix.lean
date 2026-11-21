-- Prove2me | Theorems.Thm_NymanBeurling_damped_moebius_approximation_on_each_fixed_prefix
-- name    : NymanBeurling.damped_moebius_approximation_on_each_fixed_prefix
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T01:01:22.252682+00:00
-- url     : https://prove2.me/theorems/0df230de-08d4-481a-ab04-4e43bf06a8f7
-- title:
--   Damped Möbius sums approximate every fixed finite prefix to arbitrary accuracy
-- statement:
--   For $m\ge1$, $\varepsilon>0$ and a finite truncation $N$, put
--   $$E_{N,\varepsilon}(m)=1+\sum_{d=2}^{N+1}\frac{\mu(d)}{d^\varepsilon}\frac{m\bmod d}{d}.$$
--   For each fixed integer $H\ge0$ and each $\delta>0$, all sufficiently small positive $\varepsilon<1/2$ have the following property. For all sufficiently large $N$, every $0\le h\le H$ satisfies
--   $$\sum_{m=1}^{h}\frac{E_{N,\varepsilon}(m)^2}{m(m+1)}<\delta.$$
--   The allowable damping and the truncation threshold may depend on the prescribed prefix $H$.
-- source:
--   The finite-prefix statement is an unconditional consequence of the Dirichlet series for the reciprocal Riemann zeta function in Re(s)>1, its simple pole at 1, and elementary Möbius inversion. The uniform approximation problem for the same family is https://prove2.me/theorems/cf53c71e-758a-4724-897b-66cd8091e51b .

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Filter Topology

theorem NymanBeurling.damped_moebius_approximation_on_each_fixed_prefix (H : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1/2 ∧
      ∀ᶠ N : ℕ in atTop, ∀ h : ℕ, h ≤ H →
        (∑ n ∈ Finset.range h,
          (1 + ∑ k : Fin N,
            ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
              (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by sorry
