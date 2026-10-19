-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_famSum
-- name    : MIPRE.CL.CLFun.factorOfPrefix_famSum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:06.432551+00:00
-- url     : https://prove2.me/theorems/a0d08e27-f9b5-479a-b8e2-593886c98461
-- title:
--   The factor spaces of a direct sum of CL presentations, read off a prefix, are blockwise
-- statement:
--   Let $F$ be a semiring, $\iota$ a finite index set with decidable equality (the coordinates of $V = F^\iota$), $k \in \mathbb{N}$, and $\kappa$ a finite index set with decidable equality and a bijection $e : \{0,\dots,k-1\} \times \iota \to \kappa$, so that $F^\kappa \cong (F^\iota)^k$: $x^{(i)} = (x_{e(i,j)})_{j \in \iota}$ is the $i$-th block of $x \in F^\kappa$, and $\mathrm{join}_e(v) \in F^\kappa$ is the vector with blocks $v_0, \dots, v_{k-1} \in F^\iota$. An $\ell$-level conditionally linear (CL) presentation on $F^\iota$ is the zero presentation at level $0$ or, at level $\ell + 1$, a register subspace $S \subseteq \iota$, a linear map $L_1$ on $V_S$ and a continuation choosing an $\ell$-level presentation by the value of $L_1$. The direct sum $\bigoplus_e P$ of $\ell$-level presentations $P_0, \dots, P_{k-1}$ on $F^\iota$ is the $\ell$-level presentation on $F^\kappa$ whose stages act blockwise (`famSum`). The structure lemma for CL functions attaches to a presentation its factor spaces $V_{j+1,u}$, the register subspace of stage $j+1$, determined by the prefix $u = L_{\leq j}(x)$; `factorOfPrefix j u` computes it from the prefix alone.
--
--   For every level $\ell$, every family $P$ of $\ell$-level presentations on $F^\iota$, every stage $j \in \mathbb{N}$ and every prefix $u \in F^\kappa$,
--
--   $$V_{j+1,u}\Bigl(\textstyle\bigoplus_e P\Bigr) \;=\; \mathrm{blockSet}_e\Bigl(i \mapsto V_{j+1,u^{(i)}}(P_i)\Bigr) = \bigl\{ e(i,m) : i < k,\ m \in V_{j+1,u^{(i)}}(P_i) \bigr\}.$$
--
--   A sampler's `factor` query answers with this space; the identity is one of those that let the repeated sampler of the parallel repetition theorem answer its queries blockwise.
--
--   **Formalization Note** The statement is `(famSum e ℓ P).factorOfPrefix j u = blockSet e fun i => (P i).factorOfPrefix j (block e i u)`, an equality of `Finset κ`, quantified in Lean over `ℓ : ℕ`, `P : Fin k → CLFun F ι ℓ`, `j : ℕ` and `u : κ → F`, with `e : Fin k × ι ≃ κ` explicit; no hypothesis relates `j` to `ℓ` or constrains the family. `CLFun.factorOfPrefix` is defined by recursion: `zero ↦ ∅`; `cons S _ _` at stage `0` `↦ S`; `cons S _ next` at stage `j + 1` with prefix `u` `↦ (next (proj S u)).factorOfPrefix j (proj Sᶜ u)`, `proj S` being the coordinate projection onto `V_S`; `blockSet e T :=Finset.univ.filter fun p => (e.symm p).2 ∈ T (e.symm p).1`. `F` is any `Semiring`; `ι`, `κ` carry `[DecidableEq] [Fintype]` and `k : ℕ` is implicit (the module's `variable` line). Blueprint `lem:cl-famsum`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Repeat.lean#L261-L277; blueprint lem:cl-famsum

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

theorem MIPRE.CL.CLFun.factorOfPrefix_famSum : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (j : ℕ) (u : κ → F),
    (famSum e ℓ P).factorOfPrefix j u = blockSet e fun i => (P i).factorOfPrefix j (block e i u) := by sorry
