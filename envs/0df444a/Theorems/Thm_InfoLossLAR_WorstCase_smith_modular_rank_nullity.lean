-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_smith_modular_rank_nullity
-- name    : InfoLossLAR.WorstCase.smith_modular_rank_nullity
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:32:59.959404+00:00
-- url     : https://prove2.me/theorems/13fe74da-4ad3-483a-9d4c-db52a70d0591
-- title:
--   Modular rank and nullity from Smith form
-- statement:
--   Let $q$ be prime, let $0\le r\le d$, and let $T$ be an integer $d\times d$ matrix with unimodular integer matrices $U,V$ satisfying $UTV=\operatorname{diag}(I_r,qI_{d-r})$. Then
--
--   $$\operatorname{rank}_{\mathbb F_q}(T\bmod q)=r,\qquad \dim_{\mathbb F_q}\ker(T\bmod q)=d-r.$$
--
--   This identifies the rank and nullity of a rounding matrix from its Smith data. The statement also permits $q=2$ and $d=0$.
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, https://arxiv.org/abs/2611.05136, p. 14, Lemma 2.4 (Smith-form consequences; prime-modulus and arbitrary-dimension strengthening).

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
set_option autoImplicit false

namespace InfoLossLAR.WorstCase
theorem smith_modular_rank_nullity (q r d : ℕ) [Fact q.Prime]
    (T : Matrix (Fin d) (Fin d) ℤ) (S : SmithData q r d T) :
    (matModq q T).rank = r ∧
    Module.finrank (ZMod q) (LinearMap.ker (Matrix.mulVecLin (matModq q T))) = d - r := by sorry
end InfoLossLAR.WorstCase
