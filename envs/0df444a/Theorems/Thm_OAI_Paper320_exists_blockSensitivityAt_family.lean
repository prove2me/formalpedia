-- Prove2me | Theorems.Thm_OAI_Paper320_exists_blockSensitivityAt_family
-- name    : OAI.Paper320.exists_blockSensitivityAt_family
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:53:48.077068+00:00
-- url     : https://prove2.me/theorems/2fcf693b-ec05-4e3c-a807-c2e304533ea9
-- title:
--   The block sensitivity at a point is attained by an explicit family of blocks
-- statement:
--   Let $I$ be a finite set, identify Boolean values with $\{0,1\}$, and let $f : \{0,1\}^I \to \{0,1\}$ and $x \in \{0,1\}^I$. For $B \subseteq I$ write $x^{B}$ for $x$ with the coordinates in $B$ flipped. The block sensitivity $\mathrm{bs}(f,x)$ of $f$ at $x$ is the largest size of a family of pairwise disjoint nonempty sets $B \subseteq I$ with $f(x^{B}) \ne f(x)$.
--
--   This maximum is attained: there is a family $\mathcal{B}$ of subsets of $I$ such that
--   $$
--   |\mathcal{B}| = \mathrm{bs}(f,x), \qquad A \cap B = \emptyset \ \text{ for distinct } A, B \in \mathcal{B}, \qquad B \ne \emptyset \ \text{ and } \ f(x^{B}) \ne f(x) \ \text{ for every } B \in \mathcal{B}.
--   $$
--
--   This turns the definition of block sensitivity as a maximum into a concrete optimal family of sensitive blocks, which can then be manipulated: for instance, two optimal families can be combined into product blocks for a composed function, and a positive block sensitivity yields two inputs on which $f$ differs.
--
--   **Formalization Note** `blockSensitivityAt f x` is defined as the supremum (`Finset.sup`) over all finite families `blocks : Finset (Finset I)` of the value `blocks.card` if the family is admissible and `0` otherwise. When $\mathrm{bs}(f,x) = 0$ the family is necessarily empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Basic.lean#L120-L135

import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic

open OAI OAI.Paper320
open scoped Classical
variable {I J K : Type}
variable [Fintype I]

theorem OAI.Paper320.exists_blockSensitivityAt_family (f : (I → Bool) → Bool) (x : I → Bool) :
    ∃ blocks : Finset (Finset I), blocks.card = blockSensitivityAt f x ∧
      (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) := by sorry
