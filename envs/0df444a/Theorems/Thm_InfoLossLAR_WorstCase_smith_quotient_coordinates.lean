-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_smith_quotient_coordinates
-- name    : InfoLossLAR.WorstCase.smith_quotient_coordinates
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:33:05.604198+00:00
-- url     : https://prove2.me/theorems/203c291f-212b-493e-926e-097775cc492e
-- title:
--   Smith coordinates for the image-lattice quotient
-- statement:
--   Let $q$ be prime and $0\le r\le d$. Let $T,U,V$ be integer $d\times d$ matrices with $U,V$ unimodular and $UTV=\operatorname{diag}(I_r,qI_{d-r})$. Write $P$ for the last $d-r$ rows of $U$ and $\mathcal L(T)=T\mathbb Z^d$. Then
--
--   $$z\longmapsto Pz\bmod q:\mathbb Z^d\longrightarrow\mathbb F_q^{d-r}$$
--
--   is surjective and has kernel $\mathcal L(T)$. Thus it supplies explicit coordinates for the image-lattice quotient. This includes the case $r=d$, where the codomain is the zero-dimensional space. The statement also permits $q=2$ and $d=0$.
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, https://arxiv.org/abs/2611.05136, p. 14, Lemma 2.4 (Smith-form consequences; prime-modulus and arbitrary-dimension strengthening).

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
set_option autoImplicit false

namespace InfoLossLAR.WorstCase
theorem smith_quotient_coordinates (q r d : ℕ) [Fact q.Prime]
    (T : Matrix (Fin d) (Fin d) ℤ) (S : SmithData q r d T) :
    Function.Surjective (fun z : Fin d → ℤ => modq q (S.P.mulVec z)) ∧
    (∀ z : Fin d → ℤ, modq q (S.P.mulVec z) = 0 ↔ z ∈ imageLattice T) := by sorry
end InfoLossLAR.WorstCase
