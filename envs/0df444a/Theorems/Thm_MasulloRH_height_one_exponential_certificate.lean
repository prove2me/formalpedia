-- Prove2me | Theorems.Thm_MasulloRH_height_one_exponential_certificate
-- name    : MasulloRH.height_one_exponential_certificate
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T16:40:29.805205+00:00
-- url     : https://prove2.me/theorems/6611257a-1305-4ffc-9dd5-65de0d41a834
-- title:
--   A kernel-checkable table of 494 rational exponential enclosures
-- statement:
--   Let $(x_i,\ell_i,u_i)$ be row $i$ of the published height-one rational exponential table. Every row is a valid enclosure of the actual real exponential:
--
--   $$\forall i\in\{0,\ldots,493\},\qquad \ell_i\le \exp(x_i)\le u_i.$$
--
--   The quantifier covers all 494 exact rational triples. The theorem has no hypotheses and invokes the standard real exponential, not an approximating function. Its intended proof uses finite rational Taylor remainder bounds at small arguments, exact scaling and reciprocation, and a simple bound for sufficiently negative arguments. Numerical search only selected the rational endpoints; no numerical oracle is a premise.
--
--   This finite result supplies reusable scalar inequalities for an explicit theta-energy certificate at height one. It does not assert any cofinal approximation property or the Riemann hypothesis.
--
--   **Formalization Note.** Each rational coordinate is explicitly coerced into $\mathbb R$ in the inequalities. The data definition carries no validity assertion, and the theorem states that assertion for every `Fin 494` index.
-- source:
--   Original rational endpoint certificates generated for the explicit height-one theta-energy witness, https://prove2.me/theorems/89c50384-329f-4aa2-a044-b78a04d6c29a . These are supporting finite numerical data for that contribution, not a theorem or table attributed to Masullo. The theorem proves all real exponential inequalities by rational Taylor estimates, scaling and inversion; the table alone makes no accuracy assertion.

import Definitions.Def_MasulloRH_HeightOneExponentialTable
import Mathlib.Analysis.SpecialFunctions.Exp
set_option autoImplicit false

theorem MasulloRH.height_one_exponential_certificate :
  ∀ i : Fin 494,
    ((MasulloRH.HeightOneExponentialTable.entry i).2.1 : ℝ) ≤
      Real.exp ((MasulloRH.HeightOneExponentialTable.entry i).1 : ℝ) ∧
    Real.exp ((MasulloRH.HeightOneExponentialTable.entry i).1 : ℝ) ≤
      ((MasulloRH.HeightOneExponentialTable.entry i).2.2 : ℝ) := by sorry
