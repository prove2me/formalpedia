-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_coarse32
-- name    : HlawkaSchatten.DiagonalCutoff32.coarse32
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:19:48.006312+00:00
-- url     : https://prove2.me/theorems/c1396734-69ba-4126-9311-53cdb8b8c6db
-- title:
--   Coarse orientation of a Hlawka counterexample for $p\ge 32$
-- statement:
--   Let $32\le p\le 50$ with $0.448\,p<K_p$, and let $0<q\le 0.386$ with $\mathrm{scalarEnvelope}(p,q)<K_p$. If three real vectors $x,y,z\in\mathbb R^3$ violate Hlawka's inequality with constant $K_p$ for the $\ell_p$ norm, then there is a $3\times 3$ real matrix $X$ with rows $X_0,X_1,X_2$ such that
--
--   1. entries in the coarse box: $D=[-1.158,-0.555]$ for diagonal entries and $O=[0.79,1.158]$ for off-diagonal entries;
--   2. $\|X_0\|_p+\|X_1\|_p+\|X_2\|_p=3$ and $\|X_0+X_1+X_2\|_p<3q$;
--   3. pair-gap sum below $2/(0.448\,p)$;
--   4. the triple deficit of $X$ at $K_p$ is negative.
--
--   Here violating Hlawka's inequality with constant $K$ means $(2K-1)(\|x\|_p+\|y\|_p+\|z\|_p)+\|x+y+z\|_p<K(\|x+y\|_p+\|x+z\|_p+\|y+z\|_p)$.
--
--   It is the entrance step of the localization of a counterexample.
-- source:
--   Sharp diagonal Hlawka constant campaign, cutoff-32 entry (https://prove2.me/campaigns/sharp-diagonal-hlawka-constant); definitions of the foundation mission (Ezzeri Esa, Apache-2.0).

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff32.coarse32 : ∀ p : ℝ, 32 ≤ p → p ≤ 50 →
    (448 / 1000 : ℝ) * p < cyclicConstant p →
    ∀ q : ℝ, 0 < q → q ≤ 386 / 1000 → scalarEnvelope p q < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ, hlawkaDeficit p (cyclicConstant p) x y z < 0 →
      ∃ X : Triple,
        (∀ j i, if j = i then -(1158 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555 / 1000 : ℝ)
                 else (79 / 100 : ℝ) ≤ X j i ∧ X j i ≤ (1158 / 1000 : ℝ)) ∧
        lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 ∧
        lpNorm p (X 0 + X 1 + X 2) < 3 * q ∧
        pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448 / 1000) * p) ∧
        tripleDeficit p (cyclicConstant p) X < 0 := by sorry
