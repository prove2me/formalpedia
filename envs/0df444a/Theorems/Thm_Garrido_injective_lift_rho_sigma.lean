-- Prove2me | Theorems.Thm_Garrido_injective_lift_rho_sigma
-- name    : Garrido.injective_lift_rho_sigma
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T13:59:45.094721+00:00
-- url     : https://prove2.me/theorems/c62ba6bd-a872-4257-9c8b-f96ab2a8d050
-- title:
--   Proposition 1.6, step — the rotations ρ and σ generate a free group
-- statement:
--   The homomorphism from the free group $F_2 = \langle a, b \rangle$ to
--   $SO(3,\mathbb{R})$ sending $a \mapsto \rho$ and $b \mapsto \sigma$ is injective, where
--   $\rho$ and $\sigma$ are the rotations of Proposition 1.6:
--
--   $$\rho = \begin{pmatrix} 1/3 & -2\sqrt{2}/3 & 0 \\ 2\sqrt{2}/3 & 1/3 & 0 \\ 0 & 0 & 1 \end{pmatrix}, \qquad
--   \sigma = \begin{pmatrix} 1 & 0 & 0 \\ 0 & 1/3 & -2\sqrt{2}/3 \\ 0 & 2\sqrt{2}/3 & 1/3 \end{pmatrix}.$$
--
--   Equivalently, no nonempty reduced word in $\rho^{\pm 1}$, $\sigma^{\pm 1}$ is the identity
--   matrix. This is the computational input to Proposition 1.6.
--
--   **Formalization Note.** The homomorphism is `FreeGroup.lift ![rho, sigma]`, with `rho`, `sigma`
--   the imported elements of `Matrix.specialOrthogonalGroup (Fin 3) ℝ`.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 2, proof of Proposition 1.6; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. The source gives the two rotations and refers to S. Wagon, The Banach–Tarski Paradox, Cambridge University Press (1985), Theorem 2.1, for the proof that they generate a free group; https://doi.org/10.1017/CBO9780511609596

import Mathlib
import Definitions.Def_Garrido_BanachTarski

namespace Garrido

theorem injective_lift_rho_sigma :
    Function.Injective (FreeGroup.lift ![rho, sigma]) := by
  sorry

end Garrido
