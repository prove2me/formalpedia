-- Prove2me | Theorems.Thm_LefebvreVariations_fiducial_d5
-- name    : LefebvreVariations.fiducial_d5
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:12:08.688932+00:00
-- url     : https://prove2.me/theorems/9d72a616-24b1-4332-a59f-331fb758e934
-- title:
--   Lefebvre's variations, No. 75 — on a theme by Zauner: a Weyl-Heisenberg fiducial vector exists in dimension 5
-- statement:
--   There is a unit vector $\psi\in\mathbb{C}^{5}$, indexed by $\mathbb{Z}/5$, such that for every pair $(a,b)\ne(0,0)$ in $(\mathbb{Z}/5)^2$
--   $$
--   \Bigl|\sum_{x\in\mathbb{Z}/5}\overline{\psi(x)}\,\omega^{bx}\,\psi(x+a)\Bigr|^2 \;=\; \frac{1}{6}, \qquad \omega=e^{2\pi i/5}.
--   $$
--
--   Such a Weyl-Heisenberg fiducial vector produces, by acting with the $d^2=25$ displacement operators, a symmetric informationally complete POVM (a SIC) in dimension $5$; this is the case $d=5$ of Zauner's conjecture, which asserts the existence for every $d$. The case is known to hold (an exact fiducial is known); the statement here is only its existence.
--
--   **Formalization Note** The statement has the same form as the platform's `WeylHeisenbergSIC.fiducial_exists_conjecture_c5ea` with $d=5$: a function `ψ : ZMod 5 → ℂ` with `∑ x, Complex.normSq (ψ x) = 1` and, for all `a b : ZMod 5` with `(a,b) ≠ (0,0)`, `Complex.normSq (∑ x, star (ψ x) * (ZMod.stdAddChar (b*x) * ψ (x+a))) = (((5 : ℕ) : ℝ) + 1)⁻¹`.
--
--   **Why this is a variation.** Variation on the open mission 'Zauner's Conjecture (SIC-POVMs)' (WeylHeisenbergSIC.fiducial_d_ge_3 and its companions). It is the case d = 5, stated with the parent's own Weyl-Heisenberg formulation, a finite explicit instance where the fiducial is a concrete vector of C^5 verified by 24 algebraic equations; a model for the next dimensions.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Zauner, PhD thesis, Univ. Vienna 1999, and Renes-Blume-Kohout-Scott-Caves, J. Math. Phys. 45 (2004) 2171-2180 (fiducial in dimension 5; cited from memory). Truth check: the author found a fiducial numerically for the exact convention of the statement (Levenberg-Marquardt on the 24 conditions, residual below 1e-13 in dimension 5). Origin: the open mission 'Zauner's Conjecture (SIC-POVMs)' (the Weyl-Heisenberg fiducial theorems of dimension d>=2 and d>=3).

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LefebvreVariations

/-- Zauner's conjecture in dimension 5, Weyl-Heisenberg form: a fiducial vector in `ℂ^5`. -/
theorem fiducial_d5 :
    ∃ ψ : ZMod 5 → ℂ,
      (∑ x : ZMod 5, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 5, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 5, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (((5 : ℕ) : ℝ) + 1)⁻¹ := by
  sorry

end LefebvreVariations
