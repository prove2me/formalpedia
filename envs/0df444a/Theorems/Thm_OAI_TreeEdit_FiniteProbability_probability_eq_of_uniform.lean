-- Prove2me | Theorems.Thm_OAI_TreeEdit_FiniteProbability_probability_eq_of_uniform
-- name    : OAI.TreeEdit.FiniteProbability.probability_eq_of_uniform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:42:44.231984+00:00
-- url     : https://prove2.me/theorems/3ea7710f-365a-40be-9b16-61517e7e3ad8
-- title:
--   A map whose fibres all have the same probability is uniformly distributed
-- statement:
--   For a finite set $\Omega$ and a property $E$ of its elements write
--   $\Pr_{\omega\in\Omega}[E(\omega)]=\#\{\omega\in\Omega: E(\omega)\}/|\Omega|$ for the probability of $E$ when $\omega$ is drawn uniformly at random from $\Omega$.
--
--   Let $A$ and $B$ be finite sets with $A$ nonempty, and let $f\colon A\to B$ be a map all of whose fibres are equally likely, that is, $\Pr_{a\in A}[f(a)=b]=\Pr_{a\in A}[f(a)=c]$ for all $b,c\in B$. Then for every $b\in B$
--
--   $$
--   \Pr_{a\in A}[f(a)=b]=\frac{1}{|B|}.
--   $$
--
--   In other words, if $a$ is uniform on $A$ and all values of $f(a)$ are equally likely, then $f(a)$ is uniformly distributed on $B$. This is the basic device for proving uniformity of a pushforward by a symmetry argument, for instance for surjective group homomorphisms or for the image $\sigma(u)$ of a fixed point $u$ under a uniformly random permutation $\sigma$.
--
--   **Formalization Note** `probability E` is defined as the average over the finite type of the indicator of `E`, i.e. $|A|^{-1}\sum_{a\in A}\mathbf 1_{E(a)}$. Since $b\in B$ is given, $|B|\ge1$, so the reciprocal `(Fintype.card B : ℝ)⁻¹` on the right-hand side is a genuine reciprocal.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/FiniteProbability.lean#L114-L128

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability

open OAI OAI.TreeEdit OAI.TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.FiniteProbability.probability_eq_of_uniform {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (f : A → B) (hf : ∀ b c, probability (fun a => f a = b) = probability (fun a => f a = c))
    (b : B) : probability (fun a => f a = b) = (Fintype.card B : ℝ)⁻¹ := by sorry
