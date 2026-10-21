-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_2
-- name    : InvestCommonGood.MixedTSSPE.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:20.755039+00:00
-- url     : https://prove2.me/theorems/b4a28ebe-a35a-4bac-beae-309fb3dd84c5
-- title:
--   Lemma 2, p. 23 — I decreases then increases about x̂ < min{x*, z*}, J the reverse; I < 0 below z*, I > 0 above
-- statement:
--   Let the standing assumptions and Assumptions 1, 2 (with point $z^*$) and 4 (with point $x^*$) hold, and let $I$ and $J$ be the functions (33)–(34):
--   $$I(x)=\frac{(R_r\pi)'(x)-k}{\varphi'(x)},\qquad J(x)=(R_r\pi)(x)-kx-I(x)\varphi(x).$$
--   Then
--   1. there exists $\hat x<\min\{x^*,z^*\}$ in $\mathcal I$ such that $I'(x)<0$ and $J'(x)>0$ for $x<\hat x$, and $I'(x)>0$ and $J'(x)<0$ for $x>\hat x$;
--   2. $I(x)<0$ for $x<z^*$ and $I(x)>0$ for $x>z^*$.
--
--   The shape of $I$ and $J$ is what makes the single-player threshold equations (35)–(36) and the equations (B.21)–(B.22) for $z_1$ and $q$ solvable, and it orders the points $\theta^*<\hat x<z_1<z_2$.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, p. 23, Lemma 2

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (zs xs : ℝ)
    (hS : Standing m S) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hA4 : Assumption4 m S xs) :
    (∃ xh : ℝ, IsLemma2Point m S xh ∧ xh < min xs zs) ∧
      ∀ x ∈ m.I, (x < zs → Ifun m S x < 0) ∧ (zs < x → 0 < Ifun m S x) := by sorry

end InvestCommonGood.MixedTSSPE
