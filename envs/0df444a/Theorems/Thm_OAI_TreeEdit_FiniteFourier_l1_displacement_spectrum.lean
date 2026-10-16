-- Prove2me | Theorems.Thm_OAI_TreeEdit_FiniteFourier_l1_displacement_spectrum
-- name    : OAI.TreeEdit.FiniteFourier.l1_displacement_spectrum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:02:50.713369+00:00
-- url     : https://prove2.me/theorems/7fb94fdf-c1de-4a3c-9b10-ed8eae8091e8
-- title:
--   Averaged $\ell_1$ displacement on a finite abelian group has a nonnegative character spectrum
-- statement:
--   Let $A$ be a finite abelian group and let $\widehat{A}$ be the set of its additive characters, i.e. maps $\chi : A \to \mathbb{C}$ with $\chi(0) = 1$ and $\chi(x+y) = \chi(x)\chi(y)$; the trivial character is the constant function $1$. Let $\ell_1 = \ell_1(\mathbb{N})$ be the space of real sequences $v = (v_n)_{n \ge 0}$ with $\|v\|_1 = \sum_n |v_n| < \infty$, with the distance $\|v - w\|_1$, and let $\mathbb{E}_x$ denote the uniform average over $x \in A$.
--
--   **Theorem.** For every map $F : A \to \ell_1$ there is a function $H : \widehat{A} \to \mathbb{R}$ with $H(\chi) \ge 0$ for all $\chi$ and $H(\text{trivial}) = 0$ such that for every $z \in A$
--
--   $$
--   \mathbb{E}_{x}\, \big\|F(x+z) - F(x)\big\|_1 = \sum_{\chi \in \widehat{A}} |1 - \chi(z)|^2\, H(\chi).
--   $$
--
--   In words, the average $\ell_1$ displacement caused by translating by $z$ is a nonnegative combination of the functions $z \mapsto |1-\chi(z)|^2$ over nontrivial characters. This turns metric information about an arbitrary map into $\ell_1$ into a nonnegative weighting of characters, so that the average displacement along one translation can be compared with the average displacement along others; in the edit-distance lower bound it is applied to a hypothetical low-distortion embedding.
--
--   **Formalization Note** The conclusion is the predicate `HasSpectrum` applied to the function sending $z$ to `average (fun x => dist (F (x + z)) (F x))`. Here `RealL1` is Mathlib's `lp` space of exponent $1$ over the index set of natural numbers, and characters are Mathlib's `AddChar`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/FiniteFourier.lean#L286-L307

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

theorem OAI.TreeEdit.FiniteFourier.l1_displacement_spectrum (F : A → RealL1) :
    HasSpectrum (fun z => average (fun x => dist (F (x + z)) (F x))) := by sorry
