-- Prove2me | Theorems.Thm_OAI_CHObstruction_Domination_countable_exceptions
-- name    : OAI.CHObstruction.Domination.countable_exceptions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:56:18.480543+00:00
-- url     : https://prove2.me/theorems/9ea91354-582a-4759-9fe9-f548209906e8
-- title:
--   Domination modulo countable sets along a recursive $\omega_2$-sequence of functions $\omega_1 \to \omega_1$
-- statement:
--   Let $\omega_1$ and $\omega_2$ be the first and second uncountable initial ordinals, and identify an ordinal $\alpha$ with the set of smaller ordinals. For each $\alpha < \omega_2$ fix an injection $e_\alpha : \alpha \to \omega_1$ (one exists because $|\alpha| \le \aleph_1$). By transfinite recursion on $\alpha < \omega_2$ define $f_\alpha : \omega_1 \to \omega_1$ by
--   $$
--   f_\alpha(\beta) = \sup \{\, f_\gamma(\beta) + 1 \;:\; \gamma < \alpha,\ e_\alpha(\gamma) < \beta \,\} \qquad (\beta < \omega_1),
--   $$
--   with $\sup \varnothing = 0$. The family on the right is countable (because $e_\alpha$ is injective and $\beta$ is countable) and consists of countable ordinals, so $f_\alpha(\beta) < \omega_1$.
--
--   **Theorem.** For every $\alpha < \omega_2$ and every $\gamma < \alpha$, the set of exceptions
--   $$
--   \{\, \beta < \omega_1 \;:\; f_\alpha(\beta) \le f_\gamma(\beta) \,\}
--   $$
--   is countable. Equivalently, $f_\gamma(\beta) < f_\alpha(\beta)$ for all but countably many $\beta < \omega_1$.
--
--   Thus $(f_\alpha)_{\alpha < \omega_2}$ is strictly increasing modulo countable sets. In the construction of the endpoint model this is applied with $\alpha$ and $\gamma$ the ranks of sets $c$ and $a \in c$ of rank below $\omega_2$. The tag $f_{\operatorname{rank}(x)}(\beta)$ attached to a set $x$ at the column $\beta$ then strictly decreases from $c$ to $a$ for all but countably many $\beta$, and this is what makes the coded membership diagrams valid at all but countably many columns.
--
--   **Formalization Note** The ordinals are `Alpha = {a : Ordinal // a < ω_ 2}` and `Beta = {b : Ordinal // b < ω_ 1}`. The injections are `indexEmbedding a`, chosen by `Classical.choice`, and $f_\alpha(\beta)$ is `values a b`, defined by well-founded recursion as an `iSup` over the countable type `Prior a b`. The smaller ordinal $\gamma$ is given as `g : Set.Iio a.val` and repackaged as an element of `Alpha`; the inequality compares the underlying ordinals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/Collapse.lean#L134-L149

import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse

open OAI OAI.CHObstruction OAI.CHObstruction.Domination
universe u v w
open Cardinal Ordinal Order

theorem OAI.CHObstruction.Domination.countable_exceptions (a : Alpha.{u}) (g : Set.Iio a.val) :
    {b : Beta.{u} | (values a b).val ≤ (values ⟨g.val, lt_trans g.property a.property⟩ b).val}.Countable := by sorry
