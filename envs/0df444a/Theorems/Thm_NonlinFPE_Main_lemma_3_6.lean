-- Prove2me | Theorems.Thm_NonlinFPE_Main_lemma_3_6
-- name    : NonlinFPE.Main.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:44.490977+00:00
-- url     : https://prove2.me/theorems/9b6f00e5-4c51-4211-8ae6-72d5c6b831f0
-- title:
--   Lemma 3.6, p. 20 — under (H1)′–(H3)′, the operator A₁ of (3.42) is m-accretive in L¹
-- statement:
--   Assume (H1)′–(H3)′, i.e. $x$-independent coefficients $a_{ij}(u)$, $b_i(u)$ with $\sum_{i,j}(a_{ij}(u) + u\,a_{ij}'(u))\xi_i\xi_j \ge 0$. Then the operator
--   $$A_1u = -\sum_{i,j=1}^d D^2_{ij}\big(a_{ij}(u)u\big) + \sum_{i=1}^d D_i\big(b_i(u)u\big) \ \text{ in } \mathcal D'(\mathbb R^d), \qquad D(A_1) = \{u \in L^1 : A_1u \in L^1\}, \tag{3.42}$$
--   is m-accretive in $L^1(\mathbb R^d)$.
--
--   It is the degenerate counterpart of the m-accretivity of $A$ and the hypothesis of the Crandall–Liggett theorem in Theorem 3.7.
--
--   **Formalization Note** $A_1$ is the mission's operator $A$ applied to the coefficients lifted to be constant in $x$; $\sum_i D_i(b_i(u)u)$ is $\operatorname{div}(b(u)u)$.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, Lemma 3.6, p. 20, and (3.42)

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- Lemma 3.6, p. 20, under (H1)′–(H3)′: the operator `A₁` of (3.42), i.e. the operator `A` of
(3.8)–(3.9) with the `x`-independent coefficients `a'`, `b'`, is m-accretive in `L¹`. -/
theorem lemma_3_6 {d : ℕ} (a' : Fin d → Fin d → ℝ → ℝ) (b' : Fin d → ℝ → ℝ)
    (hDeg : HypDeg a' b') :
    IsMAccretive (opA (liftA a') (liftB b')) := by sorry

end NonlinFPE.Main
