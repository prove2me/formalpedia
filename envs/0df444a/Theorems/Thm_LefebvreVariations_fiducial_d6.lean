-- Prove2me | Theorems.Thm_LefebvreVariations_fiducial_d6
-- name    : LefebvreVariations.fiducial_d6
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:12:26.735944+00:00
-- url     : https://prove2.me/theorems/b6b81a50-775c-43d1-bc86-639c2528b564
-- title:
--   Lefebvre's variations, No. 54 — on a theme by Zauner: a Weyl-Heisenberg fiducial vector exists in dimension 6
-- statement:
--   There is a unit vector $\psi\in\mathbb{C}^{6}$, indexed by $\mathbb{Z}/6$, such that for every pair $(a,b)\ne(0,0)$ in $(\mathbb{Z}/6)^2$
--   $$
--   \Bigl|\sum_{x\in\mathbb{Z}/6}\overline{\psi(x)}\,\omega^{bx}\,\psi(x+a)\Bigr|^2 \;=\; \frac{1}{7}, \qquad \omega=e^{2\pi i/6}.
--   $$
--
--   Such a Weyl-Heisenberg fiducial vector produces, by acting with the $d^2=36$ displacement operators, a symmetric informationally complete POVM (a SIC) in dimension $6$; this is the case $d=6$ of Zauner's conjecture, which asserts the existence for every $d$. The case is known to hold (an exact fiducial is known); the statement here is only its existence.
--
--   **Formalization Note** The statement has the same form as the platform's `WeylHeisenbergSIC.fiducial_exists_conjecture_c5ea` with $d=6$: a function `ψ : ZMod 6 → ℂ` with `∑ x, Complex.normSq (ψ x) = 1` and, for all `a b : ZMod 6` with `(a,b) ≠ (0,0)`, `Complex.normSq (∑ x, star (ψ x) * (ZMod.stdAddChar (b*x) * ψ (x+a))) = (((6 : ℕ) : ℝ) + 1)⁻¹`.
--
--   **Why this is a variation.** Variation on the open mission 'Zauner's Conjecture (SIC-POVMs)' (WeylHeisenbergSIC.fiducial_d_ge_3 and its companions). It is the case d = 6, stated with the parent's own Weyl-Heisenberg formulation, a finite explicit instance where the fiducial is a concrete vector of C^6 verified by 35 algebraic equations; a model for the next dimensions.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   M. Grassl, On SIC-POVMs and MUBs in dimension 6, arXiv:quant-ph/0406175 (2004), and A. J. Scott and M. Grassl, SIC-POVMs: a new computer study, J. Math. Phys. 51 (2010) 042203 (both cited from memory). Truth check: the author found a fiducial numerically for the exact convention of the statement (Levenberg-Marquardt on the 35 conditions, residual below 1e-13 in dimension 6). Origin: the open mission 'Zauner's Conjecture (SIC-POVMs)' (the Weyl-Heisenberg fiducial theorems of dimension d>=2 and d>=3).

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LefebvreVariations

/-- Zauner's conjecture in dimension 6, Weyl-Heisenberg form: a fiducial vector in `ℂ^6`. -/
theorem fiducial_d6 :
    ∃ ψ : ZMod 6 → ℂ,
      (∑ x : ZMod 6, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 6, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 6, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (((6 : ℕ) : ℝ) + 1)⁻¹ := by
  sorry

end LefebvreVariations
