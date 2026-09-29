-- Prove2me | Theorems.Thm_GeneralCK_Information_mutualInformation_eq
-- name    : GeneralCK.Information.mutualInformation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T19:34:32.413412+00:00
-- url     : https://prove2.me/theorems/78e775bf-ce25-492c-a244-b94d99ff971d
-- title:
--   Mutual information as input entropy minus average posterior entropy
-- statement:
--   Let $n\in\mathbb N$, $f:\{0,1\}^n\to\{0,1\}$, and $p\in\mathbb R$. Write $w=2^{-n}$, $m=w\sum_x\mathbf1_{f(x)=1}$, and $t_y=\sum_x\mathbf1_{f(x)=1}K_p(x,y)$. With the formalization's binary entropy $H$ in bits, $$I(f(X);Y)=H(m)-w\sum_{y\in\{0,1\}^n}H(t_y).$$ The finite-sum algebraic identity is stated for every real $p$. When $0\le p\le1$, $Y$ is uniform, $m=\Pr[f(X)=1]$, and $t_y=\Pr[f(X)=1\mid Y=y]$, so this is precisely the conditional-entropy formula for mutual information. It is the bridge from the mission's root definition to its analytic proof. Here $K_p(x,y)$ is the product over coordinates of $1-p$ for equal coordinates and $p$ for unequal coordinates.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/InformationIdentity.lean#L94-L101

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_information

open scoped BigOperators

open GeneralCK GeneralCK.Information

theorem GeneralCK.Information.mutualInformation_eq {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    mutualInformation f p = H (meanIndicator f) -
      cubeWeight n * ∑ y, H (posterior f p y) := by sorry
