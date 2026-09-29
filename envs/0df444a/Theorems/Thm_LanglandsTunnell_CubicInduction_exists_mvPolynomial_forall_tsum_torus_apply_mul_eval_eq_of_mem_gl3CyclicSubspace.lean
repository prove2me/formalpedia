-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
-- name    : LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/d2005963-2ca2-5abc-a958-19e4bcb41cd5
-- title:
--   Rationality of the two-variable torus series of a Whittaker vector
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal{O}_{\mathbb{Q}}$, let $\psi_v$ be a non-trivial additive character of the completion $\mathbb{Q}_v$ with values in $\mathbb{C}$, and let $W : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy $W(u(x,y,z)g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x$, $y$ above the diagonal and $z$ in the corner. Assume: $W$ is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$; for every open subgroup $U_v$ there is a finite set $B$ of functions such that every element of $\mathtt{gl3CyclicSubspace}\,W$ (the $\mathbb{C}$-span of the right translates $g \mapsto W(gh)$) which is right $U_v$-invariant lies in the span of $B$; and there is a homomorphism $\omega_v : \mathbb{Q}_v^\times \to \mathbb{C}^\times$ with $W(t\cdot h) = \omega_v(t)W(h)$ for scalar matrices $t$. Let $\varpi$ be an element of the valuation ring with nonzero image of valuation $\exp(-1)$, and let $\Phi \in \mathtt{gl3CyclicSubspace}\,W$ be right invariant under some open subgroup. Put $A(n_1,n_2) = \Phi(\mathrm{diag}(\varpi^{n_1+n_2},\varpi^{n_2},1))$, written as the image under the block embedding $\mathrm{GL}_2 \to \mathrm{GL}_3$ of $\mathrm{diag}(\varpi,\varpi)^{n_2}\,\mathrm{diag}(\varpi^{n_1},1)$. The conclusion asserts the existence of $N_1 \in \mathbb{Z}$, polynomials $D_1, D_2 \in \mathbb{C}[T]$ with $D_1(0) \neq 0$ and $D_2(0) \neq 0$, a polynomial $P$ in two variables over $\mathbb{C}$, and $r > 0$, such that $A(n) = 0$ whenever $n_1 < N_1$ or $n_2 < N_1$, and such that for all $X, Y \in \mathbb{C}$ with $\|X\|, \|Y\| < r$ the family $A(N_1+m_1, N_1+m_2)X^{m_1}Y^{m_2}$ indexed by $(m_1,m_2) \in \mathbb{N}^2$ is absolutely summable and $$\Bigl(\sum_{m \in \mathbb{N}^2} A(N_1+m_1,N_1+m_2)X^{m_1}Y^{m_2}\Bigr)D_1(X)D_2(Y) = P(X,Y).$$
--
--   This is the local rationality statement for the torus values of a smooth vector in the cyclic space of a Whittaker function on $\mathrm{GL}_3$ over a non-archimedean field: the generating series in the two torus coordinates is a rational function whose denominator separates into a factor in $X$ and a factor in $Y$, each non-vanishing at $0$. It feeds the comparison of the primal and dual local Rankin–Selberg integrals at the place $v$ in the cubic induction, and is used by the middle-datum statements on both the primal and the dual side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace.lean

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

theorem LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψv ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (Φ : LocalGL3 v → ℂ) (hΦ : Φ ∈ gl3CyclicSubspace W)
    (hΦsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, Φ (g * k) = Φ g) :
    let A : ℤ × ℤ → ℂ := fun n =>
      Φ (iotaGL (UnramifiedWhittaker.scalarPi
            (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
    (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ),
      D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧ 0 < r ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
        Summable (fun m : ℕ × ℕ => ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
        (∑' m : ℕ × ℕ, A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
          MvPolynomial.eval ![X, Y] P) := by sorry
