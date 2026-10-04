-- Prove2me | Theorems.Thm_LodhaMoorePrinted_eq_of_step_singleton_y_neg_one
-- name    : LodhaMoorePrinted.eq_of_step_singleton_y_neg_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T19:31:30.087777+00:00
-- url     : https://prove2.me/theorems/30028156-0a85-46eb-8c27-910730f17aee
-- title:
--   Lodha–Moore p. 9 — the only substitution from y_s⁻¹ is the unlisted expansion of y_s⁻¹
-- statement:
--   In the Lodha–Moore mission's substitution relation (`LodhaMoore.Step`), the only word obtained from the one-letter word $y_s^{-1}$ by a single substitution is $x_s^{-1}\, y_{s00}^{-1}\, y_{s01}\, y_{s1}^{-1}$, by the expansion $y_s^{-1} \Rightarrow x_s^{-1} y_{s00}^{-1} y_{s01} y_{s1}^{-1}$.
--
--   That expansion is not in the list of substitutions on p. 9. The proof of Lemma 5.2 uses it: "the case of $y_s^{-1}$ is handled similarly using the substitution $y_s^{-1} \Rightarrow x_s^{-1}y_{s00}^{-1}y_{s01}y_{s1}^{-1}$" (p. 10). The paragraph before Lemma 5.6 writes it out as well (p. 11). Without it, nothing other than $y_s^{-1}$ itself can be derived from $y_s^{-1}$, and every word derived from $y_s$ other than $y_s$ keeps the letter $y_{s10}^{-1}$. So Lemmas 5.2 and 5.4 fail for $y_s^{-1}$, and for $y_s$ once the required depth is at least $|s| + 3$. The mission's relation includes the expansion.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 9, the substitutions defining derivations (no rule for y_s⁻¹), and p. 10, the proof of Lemma 5.2

import Definitions.Def_LodhaMooreWords
import Mathlib

namespace LodhaMoorePrinted

theorem eq_of_step_singleton_y_neg_one (s : LodhaMoore.Seq) (Ω : LodhaMoore.Word)
    (h : LodhaMoore.Step [(.y s, -1)] Ω) :
    Ω = [(.x s, -1), (.y (s ++ [false, false]), -1), (.y (s ++ [false, true]), 1),
      (.y (s ++ [true]), -1)] := by
  sorry

end LodhaMoorePrinted
