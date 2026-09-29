-- Prove2me | Theorems.Thm_Garrido_treeSection_a_mul_mul_a
-- name    : Garrido.treeSection_a_mul_mul_a
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T13:08:10.699814+00:00
-- url     : https://prove2.me/theorems/139cc208-db57-4e86-aeee-720d4e4312ee
-- title:
--   p. 14 — conjugation by a maps St(1) to itself and swaps the pair (u₀, u₁)
-- statement:
--   For every $u \in St(1)$, conjugating by $a$ gives an element of $St(1)$ whose pair is that of
--   $u$, swapped: writing $u = (u_0, u_1)$,
--
--   $$aua \in St(1) \quad\text{and}\quad aua = (u_1, u_0).$$
--
--   **Formalization Note.** The pair $(u_0, u_1)$ is the imported `stOnePair`: the sections of $u$ at
--   the vertices `[false]` and `[true]`. Like the notes' notation it is defined on $St(1)$ only, so the
--   statement first provides $aua \in St(1)$ and then compares the pairs. Its components are
--   automorphisms of the tree; that they lie in $\Gamma$ is the $\psi_n$ milestone.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 14, the paragraph after Definition 4.6; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Grigorchuk

namespace Garrido

theorem treeSection_a_mul_mul_a (u : GrigorchukGroup) (hu : u ∈ levelStabilizer 1) :
    ∃ h : GrigorchukGroup.a * u * GrigorchukGroup.a ∈ levelStabilizer 1,
      stOnePair ⟨_, h⟩ = (stOnePair ⟨u, hu⟩).swap := by
  sorry

end Garrido
