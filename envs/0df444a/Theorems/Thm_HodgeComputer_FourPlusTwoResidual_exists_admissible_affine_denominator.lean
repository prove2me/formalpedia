-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_admissible_affine_denominator
-- name    : HodgeComputer.FourPlusTwoResidual.exists_admissible_affine_denominator
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T14:28:16.315525+00:00
-- url     : https://prove2.me/theorems/6273c0e9-f0a6-4ad6-b472-cdaaf6a1376a
-- title:
--   Existence of an $H$-coprime affine denominator
-- statement:
--   **Claim.** There exists a nonzero polynomial $B\in\mathbb{C}[x,y,z]$ that is not divisible by the dehomogenized four-plus-two core $h=$ `affineCore`.
--
--   Equivalently, the admissible (i.e. $H$-coprime) affine denominator locus is nonempty. The constant $B=1$ works: if $h\mid 1$ then $h$ would be a unit in $\mathbb{C}[x,y,z]$, but $h$ is non-constant (evaluate at $0$ versus at $e_0$).
--
--   **Formalization Note.** Unconditional form of the denominator half of dossier Lemma L9 / the hypothesis of `fixed_support_numerators_of_affine_swept_support`, matching the $B=1$ witness already used in `exists_affine_dehomogenized_swept_support`.
-- source:
--   hodge.computer four-plus-two residual dossier Lemma L9 / Prove2Me mission discussion; Epoch-4 wormhole split of exists_fixed_support_equation_witness

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_admissible_affine_denominator :
    ∃ (B : MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧ ¬(HodgeComputer.FourPlusTwoResidual.affineCore ∣ B) := by sorry
