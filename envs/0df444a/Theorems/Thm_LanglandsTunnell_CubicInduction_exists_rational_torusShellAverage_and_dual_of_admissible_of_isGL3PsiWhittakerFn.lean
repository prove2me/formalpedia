-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/5c570cda-2c3e-53d4-9e98-a021c4de211e
-- title:
--   Rationality of torus-shell averages of admissible Whittaker functions
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, a nontrivial additive character $\psi_v$ of $\mathbb{Q}_v$, and a function $W$ on $\mathrm{GL}_3(\mathbb{Q}_v)$ which is $\psi_v$-Whittaker in the sense that $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for the upper unipotent matrix with entries $x,y,z$ and all $g$; assume $W$ is invariant under right translation by some open subgroup, and that the span of the right translates of $W$ is admissible, i.e. for every open subgroup $U_v$ there is a finite set $B$ of functions such that every right $U_v$-invariant element of that span lies in the $\mathbb{C}$-span of $B$. Assume further $W(\mathrm{diag}(t,t,t)h)=\omega_v(t)W(h)$ for a character $\omega_v$ of $\mathbb{Q}_v^\times$, and let $\varpi$ be an integral element with nonzero image and $|\varpi|=q_v^{-1}$. Fix $b\in\mathbb{N}$. Then for every $g_3\in \mathrm{GL}_3(\mathbb{Q}_v)$, $k_0\in \mathrm{GL}_2(\mathbb{Q}_v)$, every character $\eta$ of $\mathbb{Q}_v^\times$ having conductor exponent $c$ (trivial on the $c$-th higher unit group, nontrivial on the $m$-th for each $m<c$) with $c\le b$, and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$, consider the two arrays on $\mathbb{Z}\times\mathbb{Z}$
--   $$A(n)=\int_{|u|=1}\Bigl(\int_{K_1(v^b)} W\bigl(\iota(\varpi^{n_2}I_2\cdot\mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0k)\,g_3\bigr)\,d\mu_2(k)\Bigr)\eta(u)\,d^\times u,$$
--   the level subgroup being the preimage in $\mathrm{GL}_2(\mathbb{Q}_v)$ of the finite-adelic level-one group of the ideal $v^b$ and $d^\times u$ the multiplicative measure obtained from the self-dual additive measure at $v$ by the density $|x|^{-1}$, and the analogous array $A^\vee(n)$ in which $W(\,\cdot\,g_3)$ is replaced by $y\mapsto W(w_3\,{}^t y^{-1} g_3)$ and $k$ by ${}^tk^{-1}$. The assertion is that each of $A$ and $A^\vee$ satisfies a rationality relation: there exist $N_1\in\mathbb{Z}$, polynomials $D_1,D_2\in\mathbb{C}[X]$ with $D_1(0)\neq0$, $D_2(0)\neq0$, and $M\in\mathbb{N}$, such that the array vanishes whenever $n_1<N_1$ or $n_2<N_1$, and for all $m_1,m_2\in\mathbb{N}$ with $M\le m_1$ or $M\le m_2$ the double convolution $\sum_{i}\sum_{l} D_1[i]\,D_2[l]\,A(N_1+m_1-i,\;N_1+m_2-l)=0$, the sums running over $i\le\deg D_1$, $l\le\deg D_2$.
--
--   The statement expresses, in the shape of a two-variable linear recursion with separated denominators, the finiteness of the Jacquet modules of an admissible generic representation along the two simple roots of $\mathrm{GL}_3$: the level-$b$ averaged, $\eta$-twisted shell averages of a Whittaker function along the torus are supported in a translate of the dominant cone and have rational generating series in the two shell parameters. It serves as the local input replacing a finite-support hypothesis on the torus arrays, and is used in the derivation of the rational form and functional equation of the local Rankin–Selberg integrals for $\mathrm{GL}_3\times\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn.lean

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

theorem LanglandsTunnell.CubicInduction.exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn
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
        (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
          (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
            ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
              D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)) ∧
        (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Ad n = 0) ∧
          (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
            ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
              D₁.coeff i * D₂.coeff l * Ad (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)) := by sorry
