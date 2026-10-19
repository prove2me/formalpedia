-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_primal_sq_le
-- name    : OAI.DiamondDistortion.SegmentSystem.primal_sq_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:01:24.328641+00:00
-- url     : https://prove2.me/theorems/da8f4015-f84a-4129-a9a3-19907584fb45
-- title:
--   Bounding the squared segment norm by the energies of all test families
-- statement:
--   Let $I$ be a set and let $\mathcal S$ be a collection of finite subsets of $I$, called *segments*, that contains every singleton $\{v\}$. A *test family* is a finite sequence $F=(S_1,\dots,S_n)$ ($n\ge0$) of pairwise disjoint segments. For a finitely supported function $p\colon I\to\mathbb{R}$ the *segment norm* is
--   $$\|p\|=\sup_{F}\Bigl(\sum_{i=1}^{n}\Bigl(\sum_{v\in S_i}p(v)\Bigr)^2\Bigr)^{1/2},$$
--   the supremum over all test families; it is finite (each term is at most $\sum_v|p(v)|$) and it is a norm, because singleton families give $|p(v)|\le\|p\|$.
--
--   **Theorem.** Let $p\colon I\to\mathbb{R}$ be finitely supported and let $M\ge0$. If every test family $(S_1,\dots,S_n)$ satisfies
--   $$\sum_{i=1}^{n}\Bigl(\sum_{v\in S_i}p(v)\Bigr)^2\le M,$$
--   then $\|p\|^2\le M$.
--
--   The quantity on the left is the *energy* of $p$ on the test family. The theorem is the basic tool for upper bounds on segment norms: it suffices to control the energy of one family at a time, and the square root implicit in the definition never has to be handled.
--
--   **Formalization Note** A segment system is a structure `T : SegmentSystem ι` with a predicate `IsSegment` on finite sets and the field `singleton`; test families are `T.Family`, indexed by `Fin n`, and the segment norm is `T.primalSeminorm`, the pointwise supremum of the family seminorms. Finitely supported functions are `ι →₀ ℝ`. The assumption $M\ge0$ is part of the statement; it also follows from the main hypothesis applied to the empty family ($n=0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Orthogonality.lean#L16-L30

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
universe u v
open scoped BigOperators Classical Topology
open Set
variable {ι κ : Type*} (T : SegmentSystem ι)

theorem OAI.DiamondDistortion.SegmentSystem.primal_sq_le (p : ι →₀ ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ F : T.Family, (∑ i, (∑ v ∈ F.seg i,p v)^2) ≤ M) :
    (T.primalSeminorm p)^2 ≤ M := by sorry
