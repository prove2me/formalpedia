-- Prove2me | Theorems.Thm_MFGLimit_Conc_estimate_5_7
-- name    : MFGLimit.Conc.estimate_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:12.945167+00:00
-- url     : https://prove2.me/theorems/cd05f464-122a-4a72-afa3-200f386f4fa1
-- title:
--   Equation (5.7), p. 20 — synchronous coupling and Lipschitz expectations
-- statement:
--   For $p\in[1,2]$ and an interacting drift with Lipschitz constant $L$ in (5.4), solve (5.6) from deterministic vectors $x,y\in(\mathbb R^d)^n$ using the same Brownian motions. Write $P_x,P_y$ for the two product-path laws and $\pi_{x,y}$ for their synchronous coupling. A constant $c>0$, depending only on $T,p,L$ and uniform in $n$, satisfies for every 1-Lipschitz $\Phi$,
--   $$|\langle P_x,\Phi\rangle-\langle P_y,\Phi\rangle|^p\le\int\|x'-y'\|_{n,p}^p\,\pi_{x,y}(dx',dy')\le c\|x-y\|_{n,p}^p.$$
--   This estimate controls the sensitivity of path expectations to the initial vector.
--
--   **Formalization Note** The expectation and coupling-cost integrals are asserted integrable as part of the conclusion; the coupling is built from the same noise realization. The constant is chosen before the dimension, model, population size, initial vectors, and test function.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 19–20, §5.2, (5.7)

import Mathlib
import Definitions.Def_MFGLimit_Conc_Transport

namespace MFGLimit.Conc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Equation (5.7): a dimension-uniform synchronous-coupling estimate for (5.6). -/
theorem estimate_5_7 (T : ℝ≥0) (hT : 0 < T) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 ≤ p.toReal ∧ p.toReal ≤ 2) (L : ℝ) (hL : 0 ≤ L) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d d₀ : ℕ) (Ω : Type) [mΩ : MeasurableSpace Ω],
      ∀ (M : ParticleBase Ω d d₀), M.T = T →
      ∀ (btil : ℝ≥0 → E d → Measure (E d) → E d),
        HasInteractingLipschitz M p.toReal L btil →
      ∀ (Xx : ∀ n : ℕ, (Fin n → E d) → Fin n → Ω → Path d M.T),
        (∀ n x, IsInteractingSystem M btil (fun i _ => x i) (Xx n x)) →
      ∀ (n : ℕ), 1 ≤ n → ∀ x y : Fin n → E d,
      ∀ Φ : PiLp p (fun _ : Fin n => Path d M.T) → ℝ,
        LipschitzWith 1 Φ →
        let Px := particleLaw M p (Xx n x)
        let Py := particleLaw M p (Xx n y)
        let πxy := synchronousLaw M p (Xx n x) (Xx n y)
        Integrable Φ Px ∧ Integrable Φ Py ∧
        Integrable (fun z => ‖z.1 - z.2‖ ^ p.toReal) πxy ∧
        |(∫ z, Φ z ∂Px) - (∫ z, Φ z ∂Py)| ^ p.toReal ≤
          ∫ z, ‖z.1 - z.2‖ ^ p.toReal ∂πxy ∧
        (∫ z, ‖z.1 - z.2‖ ^ p.toReal ∂πxy) ≤
          c * (stateLpNorm p (fun i => x i - y i)) ^ p.toReal := by sorry

end MFGLimit.Conc
