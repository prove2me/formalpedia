-- Prove2me | Theorems.Thm_Garrido_sum_wordLength_treeSection_le
-- name    : Garrido.sum_wordLength_treeSection_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T13:11:27.816312+00:00
-- url     : https://prove2.me/theorems/45d72e76-c045-4358-9fc9-af8b79eb3fc3
-- title:
--   Lemma 4.8 — the sections of g ∈ St(3) at level 3 have total length at most ¾ l(g) + 8
-- statement:
--   For every $g \in St(3)$, the word lengths of its eight sections at the vertices of level $3$
--   sum to at most three quarters of the length of $g$, plus $8$:
--
--   $$\sum_{i, j, k \in \{0, 1\}} l(g_{ijk}) \le \tfrac{3}{4}\, l(g) + 8, \qquad g_{ijk} = \varphi_k(\varphi_j(\varphi_i(g))).$$
--
--   This contraction of length is what makes the growth of $\Gamma$ subexponential.
--
--   **Formalization Note.** The sections are given as elements $h(v) \in \Gamma$ that coincide with
--   the imported `treeSection` at the level-3 vertex `List.ofFn v`; that they exist is part of the
--   ψₙ statement. $l$ is the imported `wordLength`, and the inequality is in $\mathbb{R}$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 14, Lemma 4.8; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Grigorchuk

namespace Garrido

theorem sum_wordLength_treeSection_le (g : GrigorchukGroup) (hg : g ∈ levelStabilizer 3)
    (h : (Fin 3 → Bool) → GrigorchukGroup)
    (hh : ∀ v, (h v : BinaryTreeAut) = treeSection (g : BinaryTreeAut) (List.ofFn v)) :
    (∑ v, (wordLength (h v) : ℝ)) ≤ 3 / 4 * (wordLength g : ℝ) + 8 := by
  sorry

end Garrido
