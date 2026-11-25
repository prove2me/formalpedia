-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_fixed_support_linear_system_solvable
-- name    : HodgeComputer.FourPlusTwoResidual.fixed_support_linear_system_solvable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T14:28:24.145985+00:00
-- url     : https://prove2.me/theorems/2cb6d103-b948-40bb-8d22-e11464c87050
-- title:
--   Macaulay solvability of affine `FixedSupportEquation` on an admissible support
-- statement:
--   **Claim.** There exist a nonzero affine denominator $B\in\mathbb{C}[x,y,z]$, a pole order $n\in\mathbb{N}$, and numerators $N=(N_0,N_1,N_2)$ such that $h\nmid B$ and the cleared fixed-support identity
--
--   $$
--   2\,B\sum_i N_i\partial_i h - 3\,h\Bigl(B\sum_i\partial_i N_i - n\sum_i N_i\partial_i B\Bigr) = 3\,y^3 B^{n+1}
--   $$
--
--   holds, where $h=$ `affineCore`.
--
--   This is the Macaulay / shivm leaf of Lemma L9: for some admissible support $(B,n)$, the linear system in the unknown numerators $N$ is solvable. Low-degree Macaulay ansätze (linear/quadratic $B$, $N$ up to the expected degree $bn-2$, structured $N=(0,f,0)$ and gradient ansätze, and $B=h+1$) are inconsistent over $\mathbb{Q}$ and over $\mathbb{F}_{32003}$; a high-degree swept-support or determinant certificate is expected.
--
--   **Formalization Note.** Same existential as `exists_fixed_support_equation_witness`; published as the dedicated linear-algebra leaf in the Epoch-4 a+b sketch.
-- source:
--   hodge.computer four-plus-two residual dossier Lemma L9; Epoch-4 wormhole/shivm split of exists_fixed_support_equation_witness

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.fixed_support_linear_system_solvable :
    ∃ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧
        ¬(HodgeComputer.FourPlusTwoResidual.affineCore ∣ B) ∧
          HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B n N := by sorry
