-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/cf2eec8a-70aa-5fca-9e21-0fb5ff6f2c1c
-- title:
--   Deep-torus vanishing of unipotent coboundaries of Whittaker functions
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$ (a height one prime of $\mathcal{O}_{\mathbb{Q}}$), let $\psi_v$ be an additive character of the completion $\mathbb{Q}_v$ with values in $\mathbb{C}$, and assume $\psi_v$ is trivial on some ball: there is $m \in \mathbb{Z}$ with $\psi_v(x) = 1$ whenever $v(x) \le \exp(m)$. Let $W : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy the left $\psi_v$-Whittaker rule $W(u(x,y,z)g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x$, $y$, $z$ in positions $(1,2)$, $(2,3)$, $(1,3)$. Let $\varpi$ be an element of the valuation ring whose image in $\mathbb{Q}_v$ is nonzero and has valuation $\exp(-1)$, i.e. a uniformiser. Write $t(n_1,n_2)$ for the image under the embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$, $h \mapsto \mathrm{diag}(h,1)$, of $\mathrm{diag}(\varpi^{n_2},\varpi^{n_2})^{\phantom{1}}\cdot \mathrm{diag}(\varpi^{n_1},1)$, that is $t(n_1,n_2) = \mathrm{diag}(\varpi^{n_1+n_2}, \varpi^{n_2}, 1)$. Let $V$ be the $\mathbb{C}$-span of the right translates $h \mapsto W(\cdot\, h)$ of $W$. Then two assertions hold. First, for every $F$ in the $\mathbb{C}$-span of the functions $g \mapsto G(g\,u(w_0,0,w_1)) - G(g)$ with $w \in \mathbb{Q}_v^2$ and $G \in V$, there exists $N_0 \in \mathbb{Z}$ such that $F(t(n_1,n_2)) = 0$ for all $n_1, n_2 \in \mathbb{Z}$ with $n_1 \ge N_0$. Second, for every $F$ in the $\mathbb{C}$-span of the functions $g \mapsto G(g\,u(0,w_1,w_0)) - G(g)$ with $w \in \mathbb{Q}_v^2$ and $G \in V$, there exists $N_0 \in \mathbb{Z}$ such that $F(t(n_1,n_2)) = 0$ for all $n_1, n_2 \in \mathbb{Z}$ with $n_2 \ge N_0$.
--
--   This is the elementary half of the asymptotic theory of Jacquet modules, in the concrete form of values of $\mathrm{GL}_3$ Whittaker functions on the diagonal torus: coboundaries along the unipotent radical of either maximal standard parabolic vanish once the corresponding torus exponent is large. It feeds the construction of polynomial relations for torus shell series of admissible Whittaker functions and, through these, the local Rankin–Selberg integral computations in the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ : ∃ m : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψv x = 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    (∀ F ∈ Submodule.span ℂ {F : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
          G ∈ gl3CyclicSubspace W ∧ F = fun g => G (g * radicalP12 w) - G g},
      ∃ N₀ : ℤ, ∀ n₁ n₂ : ℤ, N₀ ≤ n₁ →
        F (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁))) = 0) ∧
    (∀ F ∈ Submodule.span ℂ {F : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
          G ∈ gl3CyclicSubspace W ∧ F = fun g => G (g * radicalP21 w) - G g},
      ∃ N₀ : ℤ, ∀ n₁ n₂ : ℤ, N₀ ≤ n₂ →
        F (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁))) = 0) := by sorry
