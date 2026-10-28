-- Prove2me | Theorems.Thm_Measurable_fin_append
-- name    : Measurable.fin_append
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:40.961805+00:00
-- url     : https://prove2.me/theorems/f5d96546-2610-4f5a-a517-74c23c8bd354
-- title:
--   Concatenating two finite tuples is measurable
-- statement:
--   Let $(X, \mathcal F)$ be a measurable space and let $l \in \mathbb{N}$. Concatenating two
--   $l$-tuples into a $2l$-tuple,
--
--   $$
--   \bigl(X^{l} \times X^{l}\bigr) \;\longrightarrow\; X^{2l}, \qquad (u, v) \;\longmapsto\; u \frown v,
--   $$
--
--   is a measurable map, where $u \frown v$ is the tuple whose first $l$ entries are those of $u$ and
--   whose last $l$ entries are those of $v$.
--
--   Concatenation is the operation that builds a ghost sample: symmetrization arguments pair a
--   sample of size $l$ with an independent copy and then work with the combined sample of size $2l$.
--   Measurability of the pairing is the hypothesis needed to push a product measure forward along it,
--   and it is the kind of step that is invisible on paper and mandatory in a formal proof.
--
--   **Formalization Note** The map is `Fin.append`, from
--   `(Fin l → X) × (Fin l → X)` to `Fin (l + l) → X`.
-- source:
--   Elementary measurability of concatenation of finite tuples; carved from the accepted proof of BartlettNN.Sigmoid.theorem28_part1, https://prove2.me/submissions/0f39c22d-cf6c-4cef-9f8e-35718ff87eba

import Mathlib

set_option autoImplicit false

theorem Measurable.fin_append {X : Type*} [MeasurableSpace X] (l : ℕ) :
    Measurable (fun p : (Fin l → X) × (Fin l → X) => (Fin.append p.1 p.2 : Fin (l + l) → X)) := by sorry
