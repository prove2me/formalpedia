-- Prove2me | Theorems.Thm_LodhaMoore_existsUnique_conj_ys_and_image_Y0
-- name    : LodhaMoore.existsUnique_conj_ys_and_image_Y0
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T07:22:15.513991+00:00
-- url     : https://prove2.me/theorems/8d622fc9-c44b-4185-8d36-1ebf8205399d
-- title:
--   §3 — each y_s is F-conjugate to exactly one of y, y₀, y₁, y₁₀, and Y₀ is the conjugacy class of y₁₀
-- statement:
--   For every finite $s$ there is exactly one $u$ among $\langle\rangle$, $0$, $1$, $10$ such that $y_s = g^{-1}y_ug$ for some $g \in F$. The set of $y_s$ with $s$ not constant is the set of $y_s$ that are $g^{-1}y_{10}g$ for some $g \in F$.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 6, §3

import Mathlib
import Definitions.Def_LodhaMoore

namespace LodhaMoore

theorem existsUnique_conj_ys_and_image_Y0 :
    (∀ s : Seq, ∃! u : Seq, u ∈ ({[], [false], [true], [true, false]} : Set Seq) ∧
      ∃ g ∈ F, ys s = g⁻¹ * ys u * g) ∧
    ys '' {s | ¬ IsConst s} = {h | h ∈ Set.range ys ∧ ∃ g ∈ F, h = g⁻¹ * ys [true, false] * g} := by
  sorry

end LodhaMoore
