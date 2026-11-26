-- Prove2me | Theorems.Thm_OpenQuantumProblem35_hasMaximallyMixedFirstReduction_of_completion
-- name    : OpenQuantumProblem35.hasMaximallyMixedFirstReduction_of_completion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:29.525021+00:00
-- url     : https://prove2.me/theorems/2a7ace2f-7262-400e-90f2-a81b854cf074
-- title:
--   Open Quantum Problem35: has Maximally Mixed First Reduction of completion
-- statement:
--   The completion criterion gives a maximally mixed reduced state once the coefficient has the correct squared norm.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L581-L593
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L581-L593

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.hasMaximallyMixedFirstReduction_of_completion
    {n d m : ℕ} (hm : m ≤ n)
    (ψ : StateVector n d)
    (completion : Config m d → Config (n - m) d)
    (coeff : ℂ)
    (hψ : ∀ x z,
      ψ (combineFirst (n := n) (d := d) m hm x z) = if z = completion x then coeff else 0)
    (hinj : Function.Injective completion)
    (hnorm : coeff * star coeff = ((Fintype.card (Config m d) : ℂ)⁻¹)) :
    HasMaximallyMixedFirstReduction (n := n) (d := d) m hm ψ := by sorry
