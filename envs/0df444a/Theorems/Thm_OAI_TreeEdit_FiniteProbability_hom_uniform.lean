-- Prove2me | Theorems.Thm_OAI_TreeEdit_FiniteProbability_hom_uniform
-- name    : OAI.TreeEdit.FiniteProbability.hom_uniform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:43:17.625711+00:00
-- url     : https://prove2.me/theorems/cd0b938b-6ac7-4fd8-999d-676d97e5bf72
-- title:
--   A surjective homomorphism of finite groups maps the uniform distribution to the uniform distribution
-- statement:
--   Let $A$ and $B$ be finite groups, written additively but not necessarily commutative, and let $f\colon A\to B$ be a surjective group homomorphism. If $a$ is drawn uniformly at random from $A$, then $f(a)$ is uniformly distributed on $B$: for every $b\in B$
--
--   $$
--   \Pr_{a\in A}[f(a)=b]=\frac{\#\{a\in A: f(a)=b\}}{|A|}=\frac{1}{|B|}.
--   $$
--
--   Equivalently, every fibre of $f$ has exactly $|A|/|B|$ elements. In the lower-bound construction for the $\ell_1$-distortion of edit distance it is applied to maps of the form $z\mapsto a z \bmod p$ from $\mathbb Z/L\mathbb Z$ onto $\mathbb Z/p\mathbb Z$ (with $p$ a prime dividing $L$ and $p\nmid a$), to see that a uniformly random residue modulo $L$ produces a uniformly random residue modulo $p$.
--
--   **Formalization Note** The groups are Lean `AddGroup`s with `Fintype` instances and `f` is an additive homomorphism `A →+ B`. `probability E` is the uniform average of the indicator of `E` over the finite type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/FiniteProbability.lean#L229-L243

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability

open OAI OAI.TreeEdit OAI.TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.FiniteProbability.hom_uniform {A B : Type*} [AddGroup A] [AddGroup B] [Fintype A] [Fintype B]
    (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    probability (fun a => f a = b) = (Fintype.card B : ℝ)⁻¹ := by sorry
