-- Prove2me | Theorems.Thm_LefebvreVariations_fiducial_d4
-- name    : LefebvreVariations.fiducial_d4
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:11:49.100013+00:00
-- url     : https://prove2.me/theorems/171b98bc-b31a-5e32-a2e5-9cfa8c95cf2c
-- title:
--   Lefebvre's variations, No. 74 — on a theme by Zauner: a Weyl-Heisenberg fiducial vector exists in dimension 4
-- statement:
--   There is a unit vector $\psi\in\mathbb{C}^{4}$, indexed by $\mathbb{Z}/4$, such that for every pair $(a,b)\ne(0,0)$ in $(\mathbb{Z}/4)^2$
--   $$
--   \Bigl|\sum_{x\in\mathbb{Z}/4}\overline{\psi(x)}\,\omega^{bx}\,\psi(x+a)\Bigr|^2 \;=\; \frac{1}{5}, \qquad \omega=e^{2\pi i/4}.
--   $$
--
--   Such a Weyl-Heisenberg fiducial vector produces, by acting with the $d^2=16$ displacement operators, a symmetric informationally complete POVM (a SIC) in dimension $4$; this is the case $d=4$ of Zauner's conjecture, which asserts the existence for every $d$. The case is known to hold (an exact fiducial is known); the statement here is only its existence.
--
--   **Formalization Note** The statement has the same form as the platform's `WeylHeisenbergSIC.fiducial_exists_conjecture_c5ea` with $d=4$: a function `ψ : ZMod 4 → ℂ` with `∑ x, Complex.normSq (ψ x) = 1` and, for all `a b : ZMod 4` with `(a,b) ≠ (0,0)`, `Complex.normSq (∑ x, star (ψ x) * (ZMod.stdAddChar (b*x) * ψ (x+a))) = (((4 : ℕ) : ℝ) + 1)⁻¹`.
--
--   **Why this is a variation.** Variation on the open mission 'Zauner's Conjecture (SIC-POVMs)' (WeylHeisenbergSIC.fiducial_d_ge_3 and its companions). It is the case d = 4, stated with the parent's own Weyl-Heisenberg formulation, a finite explicit instance where the fiducial is a concrete vector of C^4 verified by 15 algebraic equations; a model for the next dimensions.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Zauner, Quantendesigns: Grundzuege einer nichtkommutativen Designtheorie, PhD thesis, Univ. Vienna 1999 (SIC-POVM fiducial in dimension 4; cited from memory); J. M. Renes, R. Blume-Kohout, A. J. Scott and C. M. Caves, Symmetric informationally complete quantum measurements, J. Math. Phys. 45 (2004) 2171-2180 (cited from memory: analytic solutions in small dimensions). Truth check: the author found a fiducial numerically for the exact convention of the statement (Levenberg-Marquardt on the 15 conditions, residual below 1e-13 in dimension 4). Origin: the open mission 'Zauner's Conjecture (SIC-POVMs)' (the Weyl-Heisenberg fiducial theorems of dimension d>=2 and d>=3).

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LefebvreVariations

/-- Zauner's conjecture in dimension 4, Weyl-Heisenberg form: a fiducial vector in `ℂ^4`. -/
theorem fiducial_d4 :
    ∃ ψ : ZMod 4 → ℂ,
      (∑ x : ZMod 4, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 4, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 4, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (((4 : ℕ) : ℝ) + 1)⁻¹ := by
  sorry

end LefebvreVariations
