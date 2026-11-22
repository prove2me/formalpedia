-- Prove2me | Theorems.Thm_MasulloGRH_isSchwartzLCS_of_isNuclear
-- name    : MasulloGRH.isSchwartzLCS_of_isNuclear
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:23.772777+00:00
-- url     : https://prove2.me/theorems/8e3f7840-8813-4cb0-8795-f8ce0d45c1f9
-- title:
--   Example C.1.5.10 — every nuclear locally convex space is a Schwartz space
-- statement:
--   **Nuclear spaces are Schwartz spaces (Example C.1.5.10).** Let $E$ be a nuclear locally convex space over $\mathbb C$ (nuclear spaces are Hausdorff by definition). Then $E$ is a Schwartz space in the sense of Grothendieck: for every continuous seminorm $p$ on $E$ there is a neighbourhood $V$ of $0$ in $E$ which is precompact for $p$, i.e. for every $\varepsilon>0$ there are finitely many $y_1,\dots,y_r\in E$ with
--   $$V\subset\bigcup_{i=1}^{r}\{x\in E:\ p(x-y_i)<\varepsilon\}.$$
--   Equivalently, for every closed convex circled $0$-neighbourhood $U$ there is a $0$-neighbourhood $V$ whose image in the normed space $E_U$ is precompact.
--
--   In the source this implication is what makes Grothendieck's bounded-lifting theorem for quotients of Fréchet–Schwartz spaces applicable to nuclear Fréchet spaces (proof of Corollary C.1.5.13).
--
--   The converse is false: there are Schwartz spaces, even Fréchet–Schwartz spaces, which are not nuclear. (The source's remark after Theorem C.1.5.11 that being Schwartz "implies nuclearity by Example C.1.5.10" reverses the implication.)
--
--   **Formalization Note.** Nuclearity is `MasulloGRH.IsNuclear`, which includes that $E$ is Hausdorff and locally convex (Definition C.2.4.1 of the source, via the coincidence of the projective and injective tensor product topologies); the conclusion is the new predicate `MasulloGRH.IsSchwartzLCS` from `Def_LocallyConvex_SchwartzSpace`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 668, Example C.1.5.10; classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. III, 7.2 and p. 98 (as cited by the paper)

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_LocallyConvex_SchwartzSpace

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem isSchwartzLCS_of_isNuclear (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hN : IsNuclear E) : IsSchwartzLCS E := by sorry

end MasulloGRH
