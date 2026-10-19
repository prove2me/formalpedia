-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_exactlyOn_famSum
-- name    : MIPRE.CL.CLFun.exactlyOn_famSum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:07.719158+00:00
-- url     : https://prove2.me/theorems/a7b99e40-3b91-4dd8-b845-80b6583fbc9d
-- title:
--   Exactness of a direct sum of CL presentations is blockwise
-- statement:
--   Let $F$ be a semiring, $\iota$ a finite index set with decidable equality (the coordinates of $V = F^\iota$), $k \in \mathbb{N}$, and $\kappa$ a finite index set with decidable equality and a bijection $e : \{0,\dots,k-1\} \times \iota \to \kappa$, so that $F^\kappa \cong (F^\iota)^k$: $x^{(i)} = (x_{e(i,j)})_{j \in \iota}$ is the $i$-th block of $x \in F^\kappa$, and $\mathrm{join}_e(v) \in F^\kappa$ is the vector with blocks $v_0, \dots, v_{k-1} \in F^\iota$. An $\ell$-level conditionally linear (CL) presentation on $F^\iota$ is the zero presentation at level $0$ or, at level $\ell + 1$, a register subspace $S \subseteq \iota$, a linear map $L_1$ on $V_S$ and a continuation choosing an $\ell$-level presentation by the value of $L_1$. The direct sum $\bigoplus_e P$ of $\ell$-level presentations $P_0, \dots, P_{k-1}$ on $F^\iota$ is the $\ell$-level presentation on $F^\kappa$ whose stages act blockwise (`famSum`). For $T_0, \dots, T_{k-1} \subseteq \iota$, $\mathrm{blockSet}_e(T) = \{e(i,j) : i < k,\ j \in T_i\} \subseteq \kappa$. A presentation is exact on $T$ (`ExactlyOn`) when, at level $0$, $T = \emptyset$, and at level $\ell + 1$, $S \subseteq T$ and every continuation is exact on $T \setminus S$: the register subspaces along every run partition $T$ (item (2) of `lem:cl-kth`).
--
--   For every level $\ell$, every family $P$ of $\ell$-level presentations on $F^\iota$ and every family $T$ of register subspaces of $\iota$,
--
--   $$\bigl(\forall\, i < k,\ P_i \text{ is exact on } T_i\bigr) \;\Longrightarrow\; \textstyle\bigoplus_e P \text{ is exact on } \mathrm{blockSet}_e(T).$$
--
--   Samplers are required to be exact, so this is what makes the repeated sampler of the parallel repetition theorem, the direct sum of $k$ copies of the input sampler's CL function, a sampler.
--
--   **Formalization Note** `CLFun.ExactlyOn` is defined by recursion on the presentation: `zero` is exact on `T` iff `T = ∅`; `cons S L₁ next` is exact on `T` iff `S ⊆ T ∧ ∀ v, (next v).ExactlyOn (T \ S)`. `CLFun.famSum e ℓ P` is `zero` at level `0` and, at level `ℓ + 1`, `cons (blockSet e fun i => (P i).hdS) (RegLinear.blockSum e fun i => (P i).hdL) fun v => famSum e ℓ fun i => (P i).tl (block e i v)`. Quantified in Lean over `ℓ : ℕ`, `P : Fin k → CLFun F ι ℓ` and `T : Fin k → Finset ι`, with `e : Fin k × ι ≃ κ` explicit; `F` is any `Semiring`; `ι`, `κ` carry `[DecidableEq] [Fintype]` and `k : ℕ` is implicit (the module's `variable` line). Blueprint `lem:cl-famsum`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Repeat.lean#L227-L243; blueprint lem:cl-famsum; paper linear.tex lem:cl-kth, item (2)

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

theorem MIPRE.CL.CLFun.exactlyOn_famSum : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (T : Fin k → Finset ι),
    (∀ i, (P i).ExactlyOn (T i)) → (famSum e ℓ P).ExactlyOn (blockSet e T) := by sorry
