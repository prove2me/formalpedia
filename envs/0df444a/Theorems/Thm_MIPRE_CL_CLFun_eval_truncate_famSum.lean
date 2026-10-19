-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_eval_truncate_famSum
-- name    : MIPRE.CL.CLFun.eval_truncate_famSum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:07.016075+00:00
-- url     : https://prove2.me/theorems/baaf88b3-83fe-47b2-9b6e-c997f76c3201
-- title:
--   The marginals of a direct sum of CL presentations are blockwise
-- statement:
--   Let $F$ be a semiring, $\iota$ a finite index set with decidable equality (the coordinates of $V = F^\iota$), $k \in \mathbb{N}$, and $\kappa$ a finite index set with decidable equality and a bijection $e : \{0,\dots,k-1\} \times \iota \to \kappa$, so that $F^\kappa \cong (F^\iota)^k$: $x^{(i)} = (x_{e(i,j)})_{j \in \iota}$ is the $i$-th block of $x \in F^\kappa$, and $\mathrm{join}_e(v) \in F^\kappa$ is the vector with blocks $v_0, \dots, v_{k-1} \in F^\iota$. An $\ell$-level conditionally linear (CL) presentation on $F^\iota$ is the zero presentation at level $0$ or, at level $\ell + 1$, a register subspace $S \subseteq \iota$, a linear map $L_1$ on $V_S$ and a continuation choosing an $\ell$-level presentation by the value of $L_1$. The direct sum $\bigoplus_e P$ of $\ell$-level presentations $P_0, \dots, P_{k-1}$ on $F^\iota$ is the $\ell$-level presentation on $F^\kappa$ whose stages act blockwise (`famSum`). A presentation presents the function $L(x) = L_1(x) + L_{>1,L_1(x)}(x^{S^c})$ (`eval`), and its $j$-th marginal $L_{\leq j}$ (`truncate j`) keeps its first $j$ levels, padded with trivial levels when $j$ exceeds $\ell$.
--
--   For all $j, \ell \in \mathbb{N}$, every family $P$ of $\ell$-level presentations on $F^\iota$ and every $x \in F^\kappa$,
--
--   $$\bigl(\textstyle\bigoplus_e P\bigr)_{\leq j}(x) \;=\; \mathrm{join}_e\Bigl(i \mapsto (P_i)_{\leq j}\bigl(x^{(i)}\bigr)\Bigr):$$
--
--   the $i$-th block of the $j$-th marginal of the direct sum at $x$ is the $j$-th marginal of $P_i$ at the $i$-th block of $x$. Marginals are part of a sampler's query interface; this is one of the identities that let the repeated sampler of the parallel repetition theorem answer its queries blockwise.
--
--   **Formalization Note** The statement is `((famSum e ℓ P).truncate j).eval x = join e fun i => ((P i).truncate j).eval (block e i x)`, quantified in Lean over `j ℓ : ℕ`, `P : Fin k → CLFun F ι ℓ` and `x : κ → F`, with `e : Fin k × ι ≃ κ` explicit; an equality in `κ → F` with no hypothesis on the family. `block e i x` and `join e v` are the block and assembly maps above. `CLFun.truncate j` is `zero` at `j = 0`, pads `zero` with `lift ∅` at `j + 1`, and sends `cons S L₁ next` to `cons S L₁ fun v => (next v).truncate j` at `j + 1`; `eval (cons S L₁ next) x = L₁ x + (next (L₁ x)).eval (proj Sᶜ x)`, `proj Sᶜ` zeroing the coordinates in `S`. `F` is any `Semiring`; `ι`, `κ` carry `[DecidableEq] [Fintype]` and `k : ℕ` is implicit (the module's `variable` line). Blueprint `lem:cl-famsum`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Repeat.lean#L245-L259; blueprint lem:cl-famsum

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Repeat

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
variable {ℓ : ℕ}
variable (e : Fin k × ι ≃ κ)

theorem MIPRE.CL.CLFun.eval_truncate_famSum : ∀ (j ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (x : κ → F),
    ((famSum e ℓ P).truncate j).eval x = join e fun i => ((P i).truncate j).eval (block e i x) := by sorry
