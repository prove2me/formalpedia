-- Prove2me | Theorems.Thm_MTT_Cohomology_evaluation_lattice
-- name    : MTT.Cohomology.evaluation_lattice
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T13:59:45.545728+00:00
-- url     : https://prove2.me/theorems/21fc32a6-cbbe-4747-8ec6-4c49da170bd3
-- title:
--   Finite integral lattice for algebraic cohomology evaluations
-- statement:
--   For two algebraic cohomology classes, all coefficient evaluations on [∞]−[r], divided by binomial(n,j) for 0≤j≤n, lie in a finitely generated integral lattice. The varying rational cusps introduce no denominators into integral coefficient evaluation. Base change expresses each class as a finite algebraic linear combination of integral classes, and there are only finitely many nonzero binomial denominators.
-- source:
--   Ash–Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §4, Definition 4.1 and Proposition 4.2, pp. 861–863, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf. Integral statements use relative group cohomology, not the coarse quotient at elliptic points. Elementary finite-lattice consequence of base change; the binomial denominators are explicitly retained.

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.evaluation_lattice
    {N n : ℕ} (hZ : Module.Finite ℤ (Hc N n ℤ))
    (hQ : BaseChange N n MTT.Qbar) (ψ : Bool → Hc N n MTT.Qbar) :
    (Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ n ∧
      v = evaluation j r (ψ s) / (n.choose j : MTT.Qbar)}).FG := by sorry
