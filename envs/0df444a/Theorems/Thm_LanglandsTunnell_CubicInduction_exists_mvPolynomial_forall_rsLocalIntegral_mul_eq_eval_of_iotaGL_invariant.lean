-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant
-- name    : LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b8d9d708-8113-51c3-8053-c84ff051cb1f
-- title:
--   Rationality of the local GL₃timesGL₂ Rankin–Selberg integral
-- statement:
--   Let $v$ be a height-one prime of $\mathbb{Z}=\mathcal{O}_{\mathbb{Q}}$, write $N=$ `Ideal.absNorm v.asIdeal`, and let $\theta$ be an additive character of the completion $\mathbb{Q}_v$ that is either `psiLocal` at $v$ or its inverse. Let $\varpi$ lie in the valuation ring, with nonzero image in $\mathbb{Q}_v$ of valuation $\exp(-1)$, i.e. a uniformiser. Let $W:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ satisfy $W(u(x,y,z)g)=\theta^{-1}(x+y)W(g)$ for all upper unipotent $u(x,y,z)$ and all $g$; let $W$ be right invariant under the image under `iotaGL` (the block embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$) of the local level-one subgroup at $v$ for the unit ideal, i.e. the preimage under `localEmbed` of the finite level-one subgroup; let $W$ be fixed on the right by some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$; and assume admissibility: for each open subgroup $U_v$ there is a finite set $B$ of functions such that every element of the span of the right translates of $W$ which is right $U_v$-invariant lies in the $\mathbb{C}$-span of $B$. Then there exist $P\in\mathbb{C}[X_0,X_1,X_2]$, polynomials $D_1,D_2$ with $D_1(0)\neq0$, $D_2(0)\neq0$, and $e\in\mathbb{N}$, such that (with $\mathrm{GL}_2(\mathbb{Q}_v)$ carrying its Borel structure) for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ and every Haar measure $\mu_N$ on the range of `unipotentGL2Hom` there is $c\in\mathbb{C}$ with the following property: for all $a_1,a_2\in\mathbb{C}$ and every $W_2:\mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ with $W_2(n(x)g)=\theta(x)W_2(g)$, right invariant under the local level-one subgroup at $v$ for the unit ideal, with $W_2(g\cdot\mathrm{diag}(\varpi,\varpi))=(a_1a_2/N)W_2(g)$ and $W_2(\mathrm{diag}(\varpi^m,1))=\mathrm{torusFactor}(N,a_1+a_2,a_1a_2/N)(m)$ for all $m\in\mathbb{Z}$, there is $\sigma_0\in\mathbb{R}$ such that for every $s$ with $\mathrm{Re}\,s>\sigma_0$, if $g\mapsto W(\iota g)W_2(g)\,|\det g|^{s-1/2}$ is integrable for $\mu_2$ weighted by [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_N$, then, putting $X=N^{1/2-s}$ and $Y=(a_1a_2/N)X^2$, the local integral `rsLocalIntegral` formed from these data with $\delta(g)=\mathrm{modulus}(\det g)$, $W\circ\iota$ and $W_2$ satisfies $$\Psi(s)\cdot D_1(a_1X)\,D_1(a_2X)\,D_2(Y)\,Y^e=c\cdot P(X,a_1,a_2).$$
--
--   This is the local rationality statement of Jacquet–Piatetski-Shapiro–Shalika theory for the $\mathrm{GL}_3\times\mathrm{GL}_2$ zeta integral: after clearing the two denominators $D_1,D_2$ and a monomial in $Y$, the integral becomes a single polynomial in $N^{1/2-s}$ and the two parameters $a_1,a_2$ of the $\mathrm{GL}_2$ partner, with $P$, $D_1$, $D_2$, $e$ depending only on $W$ and the constant $c$ only on the chosen Haar measures. It feeds the local functional-equation and dual-datum steps of the cubic-induction construction used in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant
    (v : HeightOneSpectrum (𝓞 ℚ))
    (θ : AddChar (v.adicCompletion ℚ) ℂ)
    (hθ : θ = NumberField.StandardAddChar.psiLocal ℚ v ∨ θ = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn θ⁻¹ W)
    (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, W (g * iotaGL k) = W g)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) :
    ∃ (P : MvPolynomial (Fin 3) ℂ) (D₁ D₂ : Polynomial ℂ) (e : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    ∃ c : ℂ,
    ∀ (a₁ a₂ : ℂ) (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (_hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        W₂ (unipotent x * g) = θ x * W₂ g)
      (_hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
      (_hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
      (_hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m),
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) →
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
          s (fun g => W (iotaGL g)) W₂ *
        (D₁.eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) * D₁.eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) *
          D₂.eval (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) ^ 2) *
          (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) ^ 2) ^ e) =
      c * MvPolynomial.eval (![(Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s), a₁, a₂] : Fin 3 → ℂ) P := by sorry
