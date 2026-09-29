-- Prove2me | Theorems.Thm_KLZ97_levelError_closed_form
-- name    : KLZ97.levelError_closed_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T12:29:51.55451+00:00
-- url     : https://prove2.me/theorems/28294767-6264-4009-967b-bad2f3c3be47
-- title:
--   Closed form of the concatenation recursion: $E_h = f^{2^h-1} p^{2^h}$
-- statement:
--   Iterating the one-level reduction $p \mapsto f p^2$ for $h$ levels of concatenation gives the closed form
--   $$E_h = f^{2^{h}-1} p^{2^{h}},$$
--   where $E_h$ is the failure parameter at concatenation level $h$ and $f$ is the number of minimal pairs of error locations that can make an encoded gate fail. This is the statement quoted in Section I.F of the paper: after $h$ iterations of the concatenation procedure the effective error is $c^{2^{h}-1} p^{2^{h}}$.
-- source:
--   Knill, Laflamme, Zurek, Resilient Quantum Computation: Error Models and Thresholds, arXiv:quant-ph/9702058v1, https://arxiv.org/abs/quant-ph/9702058, Section I.F (Concatenation), p. 6

import Mathlib
import Definitions.Def_KLZ97_model

namespace KLZ97

theorem levelError_closed_form (f p : ℝ) (h : ℕ) :
    levelError f p h = f ^ (2 ^ h - 1) * p ^ (2 ^ h) := by sorry

end KLZ97
