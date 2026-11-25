-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_fixed_support_core_solution
-- name    : HodgeComputer.FourPlusTwoResidual.exists_fixed_support_core_solution
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T05:15:13.092894+00:00
-- url     : https://prove2.me/theorems/47850091-7460-5cf4-9697-e2f7bf4970d0
-- title:
--   Existence of a fixed affine-support numerator solution for the core source
-- statement:
--   Let $h(x,y,z)=H(1,x,y,z)$ be the dehomogenized four-plus-two core (`affineCore`), and write $A_{\mathrm{aff}}=y^3$ for the corresponding affine source.
--
--   **Claim.** There exist a nonzero polynomial $B\in\mathbb{C}[x,y,z]$, a natural number $n$, and polynomials $N_0,N_1,N_2$ satisfying the cleared fixed-support identity
--
--   $$
--   2 B\sum_{i=0}^2 N_i\,\partial_i h-3 h\Bigl(B\sum_{i=0}^2\partial_i N_i-n\sum_{i=0}^2 N_i\,\partial_i B\Bigr)=3 y^3 B^{n+1}.
--   $$
--
--   In platform language this is `FixedSupportEquation B n N` with $B\neq 0$.
--
--   Geometrically $B$ is expected to arise from a projected swept-surface / sign-translate resultant of the norm-contact family (Discussion #120, Nov 22): once such $(B,n,N)$ exist, the proved theorem `coreCertificate_of_fixedSupport` yields a homogeneous `CoreCertificate`, hence a `BipartiteCoreCertificate` via `coreCertificate_iff_bipartite`. For fixed $B$ the numerator equations are linear.
--
--   **Formalization Note.** Uses `Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent`.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual`; GitHub Discussion #120 (kmehltretter82 Nov 22 swept-surface resultant / fixed-support linear numerators; benediamond contact family), https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_fixed_support_core_solution :
    ∃ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧ HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B n N := by sorry
