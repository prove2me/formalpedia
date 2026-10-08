-- Prove2me | Theorems.Thm_GivenDegreeSeq_Interior_gf_sub_le_norm1
-- name    : GivenDegreeSeq.Interior.gf_sub_le_norm1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:53:22.877172+00:00
-- url     : https://prove2.me/theorems/2ccfaca8-92cb-457c-b194-a60daf683e44
-- title:
--   $|G_f(x)-G_{f'}(x)|\le\|f-f'\|_{1'}$ on $[0,1]$
-- statement:
--   Let $f,f'\in D'[0,1]$ (here $f'$ denotes a second function, not a derivative). Then for all $0\le x\le1$,
--   $$|G_f(x)-G_{f'}(x)|\le\|f-f'\|_{1'}.$$
--
--   Consequently, if $f_n\to f$ in the modified $L^1$ norm then $G_{f_n}\to G_f$ uniformly on $[0,1]$; this is the stability step in the proof that conditions (i)–(ii) define an open set.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 24, proof of Proposition 1.2

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_DPrime

namespace GivenDegreeSeq.Interior

/-- Proof of Proposition 1.2, p. 24: for `f, f' ∈ D′[0,1]` (here `f'` is a second function, not a
derivative) and every `0 ≤ x ≤ 1`, `|G_f(x) − G_{f'}(x)| ≤ ‖f − f'‖_{1′}`. -/
theorem gf_sub_le_norm1 (f f' : ℝ → ℝ) (hf : InDprime f) (hf' : InDprime f') :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |Gf f x - Gf f' x| ≤ norm1' (f - f') := by sorry

end GivenDegreeSeq.Interior
