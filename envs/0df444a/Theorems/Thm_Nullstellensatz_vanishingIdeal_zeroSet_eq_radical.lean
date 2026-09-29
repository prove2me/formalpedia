-- Prove2me | Theorems.Thm_Nullstellensatz_vanishingIdeal_zeroSet_eq_radical
-- name    : Nullstellensatz.vanishingIdeal_zeroSet_eq_radical
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:06:30.929079+00:00
-- url     : https://prove2.me/theorems/70b84ec2-ff99-48af-abbf-8f92827d6f4e
-- title:
--   $\mathrm I(\mathrm V(J)) = \sqrt J$
-- statement:
--   Let $K$ be an algebraically closed field and $J$ an ideal of $K[X_1,\dots,X_n]$. Then
--   $$\mathrm I(\mathrm V(J)) = \sqrt J,$$
--   where $\mathrm V(J) \subseteq K^n$ is the zero locus of $J$, $\mathrm I(U)$ is the ideal of polynomials vanishing on $U$, and $\sqrt J = \{p : p^r \in J \text{ for some } r \in \mathbb N\}$ is the radical of $J$.
--
--   This is the formulation of the Nullstellensatz in the notation of algebraic geometry. The inclusion $\sqrt J \subseteq \mathrm I(\mathrm V(J))$ follows from the definitions.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Formulations", paragraph 2 (display I(V(J)) = sqrt J).

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem vanishingIdeal_zeroSet_eq_radical {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K)) :
    vanishingIdeal (zeroSet J) = J.radical := by sorry

end Nullstellensatz
