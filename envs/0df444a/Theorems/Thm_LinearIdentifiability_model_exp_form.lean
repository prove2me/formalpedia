-- Prove2me | Theorems.Thm_LinearIdentifiability_model_exp_form
-- name    : LinearIdentifiability.model_exp_form
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:37:13.316802+00:00
-- url     : https://prove2.me/theorems/fb80ab35-a7a4-4d5f-b733-72b46abd5e11
-- title:
--   Appendix C, eq. (9): the model as an exponentiated augmented inner product
-- statement:
--   Let $f:X\to\mathbb R^M$, $g:Y\to\mathbb R^M$, let $S\subseteq Y$ be a finite nonempty set, and put $Z(x,S)=\log\sum_{y'\in S}\exp(f(x)^\top g(y'))$, $\tilde f(x,S)=[-Z(x,S);f(x)]$ and $\tilde g(y)=[1;g(y)]$. Then for every $x$ and $y$
--
--   $$p(y\mid x,S)=\frac{\exp(f(x)^\top g(y))}{\sum_{y'\in S}\exp(f(x)^\top g(y'))}=\exp\big(\tilde f(x,S)^\top\tilde g(y)\big).$$
--
--   This rewrites the model as a single inner product in $\mathbb R^{M+1}$, the starting point of Appendix C.
--
--   **Formalization Note** Nonemptiness of $S$ is required: in the paper $S$ always contains the true target. For empty $S$ the left side would be a division by zero.
-- source:
--   Roeder, Metz and Kingma, On Linear Identifiability of Learned Representations, arXiv:2007.00810v3 (2020), Appendix C, eqs. (9)-(12), p. 14

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix

namespace LinearIdentifiability

theorem model_exp_form {X Y : Type*} {M : ℕ}
    (f : X → Fin M → ℝ) (g : Y → Fin M → ℝ) (x : X) (S : Finset Y) (hS : S.Nonempty) (y : Y) :
    modelProb f g x S y = Real.exp (augF f g x S ⬝ᵥ augG g y) := by sorry

end LinearIdentifiability
