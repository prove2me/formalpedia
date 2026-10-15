-- Prove2me | Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped
-- name    : MIPRE.Cost.Eval.of_append_of_wellScoped
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:11.918561+00:00
-- url     : https://prove2.me/theorems/091850f9-f13a-4008-a79c-8b267518afd0
-- title:
--   Strengthening: a well-scoped program ignores extra environment entries
-- statement:
--   Programs of the ambient model use de Bruijn variables: $\mathsf{var}\,i$ reads the $i$-th entry of the environment (a list of values), $\mathsf{elim}\,i\,n\,c$ inspects the $i$-th entry and binds its two components as variables $0$ and $1$ in $c$, $\mathsf{let}\,e\,b$ binds one variable in $b$, and $\mathsf{loop}\,b$ iterates $b$ on the state held in variable $0$. A program $p$ is *well-scoped* in $n$ variables, written $\mathsf{WellScoped}\;n\;p$, when every $\mathsf{var}\,i$ and $\mathsf{elim}\,i$ it contains has $i$ below the number of variables in scope ($n$ at the top level, $n+2$ under an $\mathsf{elim}$, $n+1$ under a $\mathsf{let}$), and every $\mathsf{loop}$ occurs with at least one variable in scope.
--
--   Let $\rho$ and $\rho'$ be environments, $p$ a program, $r$ a value and $t \in \mathbb{N}$. Suppose that $p$ is well-scoped in $|\rho|$ variables, where $|\rho|$ is the length of $\rho$, and that $p$ halts in the concatenated environment $\rho \mathbin{+\!\!+} \rho'$ with result $r$ at cost $t$. Then
--   $$ \mathsf{Eval}\;\rho\;p\;r\;t , $$
--   that is, $p$ halts in $\rho$ alone with the same result and the same cost.
--
--   This is the strengthening direction of the inertness of extra environment entries; the companion weakening lemma `Eval.append_of_wellScoped` goes the other way. It is used whenever a run of a composite program is taken apart: the backward time transfer of the efficient s-m-n map (`hardcode_time_rev`, which restricts a run of $\mathsf{let}\,(\mathsf{cons}\,(\mathsf{const}\,d)\,(\mathsf{var}\,0))\,p$ on $x$ to a run of $p$ on $(d, x)$), the Kleene fixed point and the compilation of the model to Mathlib's partial recursive functions.
--
--   **Formalization Note**: `Prog.WellScoped n p` is the recursive predicate of `Cost/Basic.lean`; the $\mathsf{loop}$ clause requires $0 < n$ because the loop rule replaces the head of the environment. Lookup beyond the end of an environment returns $\mathsf{nil}$ rather than failing, so the hypothesis of well-scopedness is what guarantees that no read reaches into $\rho'$. The cost $t$ is preserved exactly, not merely bounded.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Basic.lean#L378-L419; internal lemma of the formalization of blueprint lem:smn, https://vidick.github.io/MIPRE-formalization/blueprint/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Notation
import Definitions.Def_MIPRE_Foundations_Cost_Basic

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Eval

theorem MIPRE.Cost.Eval.of_append_of_wellScoped {env extra : Env} {p : Prog} {r : Data} {t : ℕ}
    (h : Eval (env ++ extra) p r t) (hp : p.WellScoped env.length) : Eval env p r t := by sorry
