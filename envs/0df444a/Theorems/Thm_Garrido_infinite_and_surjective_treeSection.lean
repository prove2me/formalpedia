-- Prove2me | Theorems.Thm_Garrido_infinite_and_surjective_treeSection
-- name    : Garrido.infinite_and_surjective_treeSection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T13:09:20.383967+00:00
-- url     : https://prove2.me/theorems/48c31ecd-fc5a-4dd1-9c93-9e7ff40a88ab
-- title:
--   p. 14 — Γ is infinite, since St(1) maps onto Γ
-- statement:
--   $\Gamma$ is infinite; indeed, for each first-level vertex $i \in \{0, 1\}$, every element of
--   $\Gamma$ is the section at $i$ of some element of $St(1)$:
--
--   $$|\Gamma| = \infty, \qquad \varphi_0(St(1)) = \varphi_1(St(1)) = \Gamma.$$
--
--   **Formalization Note.** $\varphi_i(g)$ is the imported `treeSection` at `[i]`, and the statement
--   asserts that every $x \in \Gamma$ equals $\varphi_i(g)$ for some $g \in St(1)$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 14, the Remark after Definition 4.6; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Grigorchuk

namespace Garrido

theorem infinite_and_surjective_treeSection :
    Infinite GrigorchukGroup ∧
      ∀ (i : Bool) (x : GrigorchukGroup), ∃ g : GrigorchukGroup, g ∈ levelStabilizer 1 ∧
        treeSection (g : BinaryTreeAut) [i] = x := by
  sorry

end Garrido
