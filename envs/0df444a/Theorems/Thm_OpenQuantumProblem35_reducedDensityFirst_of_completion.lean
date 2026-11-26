-- Prove2me | Theorems.Thm_OpenQuantumProblem35_reducedDensityFirst_of_completion
-- name    : OpenQuantumProblem35.reducedDensityFirst_of_completion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:06.118577+00:00
-- url     : https://prove2.me/theorems/39706fac-730f-5d3b-b782-1463202be1e5
-- title:
--   Open Quantum Problem35: reduced Density First of completion
-- statement:
--   A uniform superposition over the graph of an injective completion map has reduced density matrix $(c\overline c) I$ on the first subsystem.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L534-L578
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L534-L578

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.reducedDensityFirst_of_completion
    {n d m : ℕ} (hm : m ≤ n)
    (ψ : StateVector n d)
    (completion : Config m d → Config (n - m) d)
    (coeff : ℂ)
    (hψ : ∀ x z,
      ψ (combineFirst (n := n) (d := d) m hm x z) = if z = completion x then coeff else 0)
    (hinj : Function.Injective completion) :
    reducedDensityFirst (n := n) (d := d) m hm ψ =
      (coeff * star coeff) • (1 : Matrix (Config m d) (Config m d) ℂ) := by sorry
