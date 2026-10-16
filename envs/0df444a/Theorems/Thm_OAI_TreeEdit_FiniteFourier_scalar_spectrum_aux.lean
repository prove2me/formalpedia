-- Prove2me | Theorems.Thm_OAI_TreeEdit_FiniteFourier_scalar_spectrum_aux
-- name    : OAI.TreeEdit.FiniteFourier.scalar_spectrum_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:01:14.74217+00:00
-- url     : https://prove2.me/theorems/d098d0e2-868c-436c-9b98-a440e3845e9a
-- title:
--   Averaged absolute differences of a finitely-valued function are nonnegative combinations of $|1-\chi|^2$
-- statement:
--   Let $A$ be a finite abelian group and let $\widehat{A}$ be the set of its additive characters, i.e. maps $\chi : A \to \mathbb{C}$ with $\chi(0) = 1$ and $\chi(x+y) = \chi(x)\chi(y)$; the trivial character is the constant function $1$. For $\chi \in \widehat{A}$ and $z \in A$ put $\mu_\chi(z) = |1-\chi(z)|^2$, and write $\mathbb{E}_x$ for the uniform average over $x \in A$. Say that a function $V : A \to \mathbb{R}$ *has a spectrum* if there is $H : \widehat{A} \to \mathbb{R}$ with $H(\chi) \ge 0$ for all $\chi$, $H(\text{trivial}) = 0$, and $V(z) = \sum_{\chi \in \widehat{A}} \mu_\chi(z) H(\chi)$ for all $z \in A$.
--
--   **Theorem.** Let $S \subset \mathbb{R}$ be a finite set and $g : A \to \mathbb{R}$ a function with $g(x) \in S$ for all $x \in A$. Then the function
--
--   $$
--   V_g(z) = \mathbb{E}_{x}\, \big|g(x+z) - g(x)\big| \qquad (z \in A)
--   $$
--
--   has a spectrum, i.e. $V_g(z) = \sum_{\chi} |1-\chi(z)|^2 H(\chi)$ for some $H \ge 0$ vanishing at the trivial character.
--
--   Since every function on a finite group takes finitely many values, this applies to every $g : A \to \mathbb{R}$ (take $S = g(A)$). It is the scalar case of the spectral representation of averaged $\ell_1$ displacements, which converts metric information about maps into a nonnegative weighting of characters.
--
--   **Formalization Note** The finite set $S$ is an explicit parameter so that the statement can be proved by induction on $S$. Characters are Mathlib's `AddChar`, the trivial one being `0` in the additive group of characters; the conclusion is the predicate `HasSpectrum`, and $\mu_\chi$ is `multiplier`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/FiniteFourier.lean#L145-L191

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier

open OAI OAI.TreeEdit OAI.TreeEdit.FiniteFourier
universe u
attribute [local instance] Classical.propDecidable
open scoped ComplexConjugate
open RCLike
variable {A : Type*} [Fintype A] [AddCommGroup A]

theorem OAI.TreeEdit.FiniteFourier.scalar_spectrum_aux (s : Finset ℝ) :
    ∀ g : A → ℝ, (∀ x, g x ∈ s) →
      HasSpectrum (fun z => average (fun x => |g (x + z) - g x|)) := by sorry
