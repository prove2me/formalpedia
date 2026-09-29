-- Prove2me | Theorems.Thm_GeneralCK_jointMass_sum
-- name    : GeneralCK.jointMass_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T19:31:36.09633+00:00
-- url     : https://prove2.me/theorems/d0d1eebe-1d40-48db-a581-30eed6df6a96
-- title:
--   Normalization of the joint Boolean-summary and channel-output mass
-- statement:
--   Let $n\in\mathbb N$, $f:\{0,1\}^n\to\{0,1\}$, and $p\in\mathbb R$. With $q(b,y)=2^{-n}\sum_x\mathbf1_{f(x)=b}K_p(x,y)$, $$\sum_{b\in\{0,1\}}\sum_{y\in\{0,1\}^n}q(b,y)=1.$$ This algebraic identity holds for every real $p$ and includes dimension zero. In the probability range $0\le p\le1$, $q$ is the joint distribution of the one-bit summary of a uniform input and its noisy channel output. The result supplies the normalization needed for the subsequent entropy identities. Here $K_p(x,y)$ is the product over coordinates of $1-p$ for equal coordinates and $p$ for unequal coordinates.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Distribution.lean#L34-L45

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement

open scoped BigOperators

open GeneralCK

theorem GeneralCK.jointMass_sum {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    ∑ b, ∑ y, jointMass f p b y = 1 := by sorry
