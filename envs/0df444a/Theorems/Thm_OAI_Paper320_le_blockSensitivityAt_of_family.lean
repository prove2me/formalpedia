-- Prove2me | Theorems.Thm_OAI_Paper320_le_blockSensitivityAt_of_family
-- name    : OAI.Paper320.le_blockSensitivityAt_of_family
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:54:44.850391+00:00
-- url     : https://prove2.me/theorems/1fbb7d66-730d-4587-8c16-81780dd003c5
-- title:
--   An indexed family of disjoint sensitive blocks bounds block sensitivity from below
-- statement:
--   Let $I$ and $K$ be finite sets, identify Boolean values with $\{0,1\}$, and let $f : \{0,1\}^I \to \{0,1\}$ and $x \in \{0,1\}^I$. For $B \subseteq I$ write $x^{B}$ for $x$ with the coordinates in $B$ flipped, and let $\mathrm{bs}(f,x)$ be the block sensitivity of $f$ at $x$: the largest number of pairwise disjoint nonempty sets $B \subseteq I$ with $f(x^{B}) \ne f(x)$.
--
--   Let $(B_k)_{k \in K}$ be subsets of $I$ such that
--
--   - every $B_k$ is nonempty,
--   - $B_k \cap B_l = \emptyset$ whenever $k \ne l$, and
--   - $f(x^{B_k}) \ne f(x)$ for every $k \in K$.
--
--   Then
--   $$
--   |K| \le \mathrm{bs}(f,x) .
--   $$
--
--   This is the standard way to certify a lower bound on block sensitivity by an explicitly indexed family of blocks. It is applied to the lifted tower blocks of the construction separating block sensitivity from sensitivity, to product blocks of composed functions, to the singleton blocks of an OR, and to transport block families along a bijection of coordinates.
--
--   **Formalization Note** The blocks are a function `blocks : K → Finset I`, and disjointness is `Pairwise fun k l => Disjoint (blocks k) (blocks l)`. The definition of `blockSensitivityAt` maximizes over families of sets (`Finset (Finset I)`), whereas here the blocks are indexed by the finite type $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Basic.lean#L137-L158

import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic

open OAI OAI.Paper320
open scoped Classical
variable {I J K : Type}
variable [Fintype I]

theorem OAI.Paper320.le_blockSensitivityAt_of_family [Fintype K]
    (f : (I → Bool) → Bool) (x : I → Bool) (blocks : K → Finset I)
    (hne : ∀ k, (blocks k).Nonempty)
    (hd : Pairwise fun k l => Disjoint (blocks k) (blocks l))
    (hb : ∀ k, f (flip x (blocks k)) ≠ f x) :
    Fintype.card K ≤ blockSensitivityAt f x := by sorry
