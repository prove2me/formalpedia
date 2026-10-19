-- Prove2me | Theorems.Thm_MIPRE_CL_clDist_famSum
-- name    : MIPRE.CL.clDist_famSum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:21.942992+00:00
-- url     : https://prove2.me/theorems/e95790f8-94bf-4eea-b9a2-4b3fb718e5f0
-- title:
--   The conditionally linear distribution of a direct sum is the product of the blocks' distributions
-- statement:
--   Let $F$ be a finite semiring with decidable equality, $\iota$ a finite index set with decidable equality, $k \in \mathbb{N}$, and $\kappa$ a finite index set with decidable equality together with a bijection $e : \{0,\dots,k-1\} \times \iota \to \kappa$, so that $F^\kappa \cong (F^\iota)^k$; write $x^{(i)} = (x_{e(i,j)})_{j \in \iota}$ for the $i$-th block of $x \in F^\kappa$. For two functions $L, R : F^\kappa \to F^\kappa$, the conditionally linear distribution $\mathrm{clDist}(L, R)$ is the law of the pair $(L(x), R(x))$ for $x$ uniformly random in $F^\kappa$: $\mathrm{clDist}(L,R)(a,b) = |\{x \in F^\kappa : L(x) = a,\ R(x) = b\}| \,/\, |F^\kappa|$. It is the format of the question distribution of a game whose questions are sampled by CL functions. Let $L_0, \dots, L_{k-1}$ and $R_0, \dots, R_{k-1}$ be $\ell$-level CL presentations on $F^\iota$, and $\bigoplus_e L$, $\bigoplus_e R$ their direct sums (`famSum`), the $\ell$-level presentations on $F^\kappa$ whose stages act blockwise.
--
--   For all $a, b \in F^\kappa$,
--
--   $$\mathrm{clDist}\Bigl(\textstyle\bigoplus_e L,\ \bigoplus_e R\Bigr)(a, b) \;=\; \prod_{i<k} \mathrm{clDist}\bigl(L_i, R_i\bigr)\bigl(a^{(i)}, b^{(i)}\bigr).$$
--
--   The game whose question distribution is the CL distribution of the direct sums is therefore the direct repetition of the game of the blocks: this is the link between the repeated sampler of the parallel repetition theorem and the direct repetition of games, to which the game-level repetition theorem applies.
--
--   **Formalization Note** `clDist L R a b := ((Finset.univ.filter fun x => L x = a ∧ R x = b).card : ℝ) / Fintype.card (κ → F)`, a real number. The statement applies it to the evaluated presentations `(CLFun.famSum e ℓ L).eval` and `(CLFun.famSum e ℓ R).eval`, and its right-hand side is `∏ i, clDist (L i).eval (R i).eval (block e i a) (block e i b)` over `i : Fin k`. Arguments: `[Fintype F] [DecidableEq F]`, `e : Fin k × ι ≃ κ` explicit, `{ℓ : ℕ}` implicit, `L R : Fin k → CLFun F ι ℓ`, `a b : κ → F`; `F` is a `Semiring`, `ι` and `κ` carry `[DecidableEq] [Fintype]`, and `k : ℕ` is implicit, from the module's `variable` declaration. No further hypothesis is assumed (in particular `F` is not assumed nonempty). Blueprint `lem:cl-famsum`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Repeat.lean#L312-L329; blueprint lem:cl-famsum

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
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}

theorem MIPRE.CL.clDist_famSum [Fintype F] [DecidableEq F] (e : Fin k × ι ≃ κ) {ℓ : ℕ}
    (L R : Fin k → CLFun F ι ℓ) (a b : κ → F) :
    clDist (CLFun.famSum e ℓ L).eval (CLFun.famSum e ℓ R).eval a b =
      ∏ i, clDist (L i).eval (R i).eval (block e i a) (block e i b) := by sorry
