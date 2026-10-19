-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_famSum
-- name    : MIPRE.CL.CLFun.mapOfPrefix_famSum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:06.4248+00:00
-- url     : https://prove2.me/theorems/1e3e3497-a5e5-47a8-9256-0a34c2055def
-- title:
--   The stage maps of a direct sum of CL presentations, read off a prefix, are blockwise
-- statement:
--   Let $F$ be a semiring, $\iota$ a finite index set with decidable equality (the coordinates of $V = F^\iota$), $k \in \mathbb{N}$, and $\kappa$ a finite index set with decidable equality and a bijection $e : \{0,\dots,k-1\} \times \iota \to \kappa$, so that $F^\kappa \cong (F^\iota)^k$: $x^{(i)} = (x_{e(i,j)})_{j \in \iota}$ is the $i$-th block of $x \in F^\kappa$, and $\mathrm{join}_e(v) \in F^\kappa$ is the vector with blocks $v_0, \dots, v_{k-1} \in F^\iota$. An $\ell$-level conditionally linear (CL) presentation on $F^\iota$ is the zero presentation at level $0$ or, at level $\ell + 1$, a register subspace $S \subseteq \iota$, a linear map $L_1$ on $V_S$ and a continuation choosing an $\ell$-level presentation by the value of $L_1$. The direct sum $\bigoplus_e P$ of $\ell$-level presentations $P_0, \dots, P_{k-1}$ on $F^\iota$ is the $\ell$-level presentation on $F^\kappa$ whose stages act blockwise (`famSum`). The structure lemma for CL functions attaches to a presentation its stage maps $L_{j+1,u}$, the linear map of stage $j+1$ given the prefix $u = L_{\leq j}(x)$; `mapOfPrefix j u` computes it from the prefix alone.
--
--   For every $\ell$, every family $P$ of $\ell$-level presentations on $F^\iota$, every $j \in \mathbb{N}$ and all $u, y \in F^\kappa$,
--
--   $$L_{j+1,u}\Bigl(\textstyle\bigoplus_e P\Bigr)(y) \;=\; \mathrm{join}_e\Bigl(i \mapsto L_{j+1,u^{(i)}}(P_i)\bigl(y^{(i)}\bigr)\Bigr).$$
--
--   A sampler's `linear` query answers with this map; the identity is one of those that let the repeated sampler of the parallel repetition theorem answer its queries blockwise.
--
--   **Formalization Note** The statement is `(famSum e ℓ P).mapOfPrefix j u y = join e fun i => (P i).mapOfPrefix j (block e i u) (block e i y)`, an equality in `κ → F`, the linear maps `mapOfPrefix j u : (κ → F) →ₗ[F] (κ → F)` being applied to `y`, quantified in Lean over `ℓ : ℕ`, `P : Fin k → CLFun F ι ℓ`, `j : ℕ` and `u y : κ → F`, with `e : Fin k × ι ≃ κ` explicit; no hypothesis relates `j` to `ℓ` or constrains the family. `CLFun.mapOfPrefix` by recursion: `zero ↦ 0`; `cons _ L₁ _` at stage `0` `↦ L₁.toLinearMap`; `cons S _ next` at stage `j + 1` `↦ (next (proj S u)).mapOfPrefix j (proj Sᶜ u)`, `proj S` being the coordinate projection onto `V_S` and `L₁ : RegLinear F S` a linear endomorphism `L` of `ι → F` with `proj S ∘ L ∘ proj S = L`. `F` is any `Semiring`; `ι`, `κ` carry `[DecidableEq] [Fintype]` and `k : ℕ` is implicit (the module's `variable` line). Blueprint `lem:cl-famsum`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Repeat.lean#L279-L294; blueprint lem:cl-famsum

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

theorem MIPRE.CL.CLFun.mapOfPrefix_famSum : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (j : ℕ) (u y : κ → F),
    (famSum e ℓ P).mapOfPrefix j u y = join e fun i => (P i).mapOfPrefix j (block e i u) (block e i y) := by sorry
