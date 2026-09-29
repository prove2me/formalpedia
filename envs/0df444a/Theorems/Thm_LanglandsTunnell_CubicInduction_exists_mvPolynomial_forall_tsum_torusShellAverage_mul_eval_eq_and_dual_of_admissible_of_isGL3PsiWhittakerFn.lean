-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_tsum_torusShellAverage_mul_eval_eq_and_dual_of_admissible_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_tsum_torusShellAverage_mul_eval_eq_and_dual_of_admissible_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/70f1840d-bbff-52d2-a5ae-4bd8662c032c
-- title:
--   Rationality of two-variable torus-shell Whittaker series
-- statement:
--   Let $v$ be a nonzero prime of $\mathbb Z$, $\psi_v$ a nontrivial additive character of $\mathbb Q_v$, and $W:\mathrm{GL}_3(\mathbb Q_v)\to\mathbb C$ a function with $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x,y,z$. Assume: $W$ is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb Q_v)$; for every open subgroup $U_v$ there is a finite set $B$ of functions such that each element of the span of the right translates of $W$ that is right $U_v$-invariant lies in the $\mathbb C$-span of $B$; $W(\mathrm{diag}(t,t,t)h)=\omega_v(t)W(h)$ for a homomorphism $\omega_v:\mathbb Q_v^\times\to\mathbb C^\times$; and $\varpi$ is an element of the valuation ring whose image in $\mathbb Q_v$ is nonzero of valuation $\exp(-1)$. Fix $b\in\mathbb N$. Then for every $g_3\in\mathrm{GL}_3(\mathbb Q_v)$, every $k_0\in\mathrm{GL}_2(\mathbb Q_v)$, every homomorphism $\eta:\mathbb Q_v^\times\to\mathbb C^\times$ trivial on the $c$-th higher unit group and nontrivial on each smaller one with $c\le b$, and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_v)$ (taken with its Borel structure), consider the two arrays $A,A^\vee:\mathbb Z^2\to\mathbb C$ obtained by integrating, over the units $u$ with $|u|=1$ against the multiplicative measure pulled back from $|x|^{-1}\,dx$ for the self-dual additive Haar measure at $v$, the product of $\eta(u)$ with the $\mu_2$-integral over $k$ in the local level-one subgroup of level $v^b$ (the pullback of the finite-adelic level-one subgroup along the local embedding) of $W\bigl(\iota(\varpi^{n_2}I_2\cdot\mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0k)\,g_3\bigr)$, respectively of $g\mapsto W(w_3\,{}^t g^{-1}g_3)$ evaluated at the same torus element with $k$ replaced by ${}^tk^{-1}$. The assertion is that each of the two arrays has a rational two-variable generating series near the origin: there exist $N_1\in\mathbb Z$, polynomials $D_1,D_2$ with $D_1(0)\neq0$, $D_2(0)\neq0$, a polynomial $P$ in two variables and $r>0$ such that the array vanishes whenever $n_1<N_1$ or $n_2<N_1$, and for $\|X\|,\|Y\|<r$ the series $\sum_{m\in\mathbb N^2}A(N_1+m_1,N_1+m_2)X^{m_1}Y^{m_2}$ is absolutely summable and its sum times $D_1(X)D_2(Y)$ equals $P(X,Y)$.
--
--   This is the rationality statement for the local Rankin–Selberg torus sums attached to a Whittaker vector on $\mathrm{GL}_3$: the shell averages, weighted by a ramified character $\eta$ of conductor at most the depth $b$ and averaged over a level-one subgroup at $v$, assemble into power series which are rational functions of the two torus variables, the substitutions $X,Y\mapsto$ powers of $q^{\pm s}$ giving meaning to the $(3,1)$ local integrals beyond their region of convergence. It feeds the construction of the dual middle datum used in the local functional equation at $v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_tsum_torusShellAverage_mul_eval_eq_and_dual_of_admissible_of_isGL3PsiWhittakerFn.lean

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

theorem LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_tsum_torusShellAverage_mul_eval_eq_and_dual_of_admissible_of_isGL3PsiWhittakerFn
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
    (b : ℕ) :
    ∀ (g₃ : LocalGL3 v) (k₀ : GL (Fin 2) (v.adicCompletion ℚ)) (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η c → c ≤ b →
      letI := localBorel ℚ v
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let A : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                W (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        let Ad : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ),
          D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧ 0 < r ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
            Summable (fun m : ℕ × ℕ => ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
              MvPolynomial.eval ![X, Y] P) ∧
        (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ),
          D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧ 0 < r ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Ad n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
            Summable (fun m : ℕ × ℕ => ‖Ad (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, Ad (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
              MvPolynomial.eval ![X, Y] P) := by sorry
