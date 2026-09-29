-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_localLevelOne_bump_of_forall_apply_diagZ_mul_scalarPi_zpow_eq_ite
-- name    : LanglandsTunnell.RankinSelberg.localLevelOne_bump_of_forall_apply_diagZ_mul_scalarPi_zpow_eq_ite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/c251d737-ce04-5f48-9abe-68f0cae7d7a8
-- title:
--   Support and normalisation of a local ψ-bump on GL₂
-- statement:
--   Let $v$ be a height-one prime of $\mathcal O_{\mathbb Q}$, and let $\varpi$ be an element of the valuation ring $\mathcal O_v$ of the completion $\mathbb Q_v$ whose image in $\mathbb Q_v$ is nonzero and has valuation $\exp(-1)$, i.e. a uniformiser. Let $f : GL_2(\mathbb Q_v) \to \mathbb C$ satisfy three conditions: (i) $f(\mathrm{unipotent}(x)\,g) = \psi_v^{-1}(x)\, f(g)$ for all $x \in \mathbb Q_v$ and $g \in GL_2(\mathbb Q_v)$, where $\mathrm{unipotent}(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_v =$ [`NumberField.StandardAddChar.psiLocal`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) is the standard adelic additive character composed with the map placing an element of $\mathbb Q_v$ at the place $v$; (ii) $f(gk) = f(g)$ for every $g$ and every $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the subgroup of those $k$ whose image under the embedding of $GL_2(\mathbb Q_v)$ into $GL_2$ of the finite adeles (identity away from $v$) lies in the level-one subgroup for the unit ideal, i.e. both $k$ and $k^{-1}$ satisfy the predicate `IsLevelOneMatrix` at the unit ideal; (iii) for all integers $m, n$, $f\bigl(\mathrm{diag}(\varpi^{m-n},1)\cdot(\varpi I_2)^{n}\bigr)$ equals $1$ if $m = 0$ and $n = 0$, and $0$ otherwise. The conclusion is the conjunction of three assertions: $f(hk) = f(h)$ for all $k$ in that subgroup and all $h$ (condition (ii) with the quantifiers in the other order); whenever $f(h) \ne 0$ there are $x \in \mathbb Q_v$ and $k$ in that subgroup with $h = \begin{pmatrix}1&x\\0&1\end{pmatrix} k$, the unipotent factor formed by [`AutomorphicForm.unipotentGL2`](def/AutomorphicForm_ConstantTerm.html#L17); and $f(1) = 1$.
--
--   The statement says that a function on $GL_2(\mathbb Q_v)$ transforming by $\psi_v^{-1}$ under the upper unipotent subgroup, right invariant under the local level-one subgroup at $v$, and taking the indicated values on the diagonal torus, is a $\psi$-bump: right invariant, supported in $N_2 K_v$, and normalised at the identity. It supplies, in the form demanded there, the bump hypothesis of the local Rankin–Selberg computation [`LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_congruenceK1_invariant_iotaGL_eq_bump_of_localZeta31_fe_one`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_congruenceK1_invariant_iotaGL_eq_bump_of_localZeta31_fe_one), the support clause coming from the Iwasawa decomposition [`LocalGL2.iwasawa_decomposition`](thm.html#LocalGL2.iwasawa_decomposition) over the local ring at $v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_localLevelOne_bump_of_forall_apply_diagZ_mul_scalarPi_zpow_eq_ite.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AdelicDock UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.localLevelOne_bump_of_forall_apply_diagZ_mul_scalarPi_zpow_eq_ite
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hfψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      f (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * f g)
    (hfK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → f (g * k) = f g)
    (htorus : ∀ m n : ℤ,
      f (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (m - n) *
          scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n) =
        if m = 0 ∧ n = 0 then 1 else 0) :
    (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), f (h * k) = f h) ∧
    (∀ h : GL (Fin 2) (v.adicCompletion ℚ), f h ≠ 0 →
      ∃ x : v.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        h = AutomorphicForm.unipotentGL2 x * k) ∧
    f 1 = 1 := by sorry
