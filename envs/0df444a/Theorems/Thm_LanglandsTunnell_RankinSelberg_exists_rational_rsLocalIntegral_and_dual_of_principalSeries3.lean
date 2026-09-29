-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_principalSeries3
-- name    : LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_principalSeries3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/936bd03c-64d9-5942-95bb-3ef05529ab3d
-- title:
--   Rationality of local Rankin–Selberg integrals for GL₃ principal series
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal{O}_{\mathbb Q}$, write $\mathbb Q_p$ for the completion and $q=\mathrm{absNorm}(p)$. Let $\lambda_0,\lambda_1,\lambda_2$ and $\omega_3$ be characters $\mathbb Q_p^\times\to\mathbb C^\times$ with $\lambda_0\lambda_1\lambda_2=\omega_3$, each $\lambda_i$ locally constant and of absolute value $1$. Let $W_2:\mathrm{GL}_3(\mathbb Q_p)\to\mathbb C$ be a function assumed to be a matrix coefficient $g\mapsto\Lambda(f(\,\cdot\,g))$ of some $\mathbb C$-linear functional $\Lambda$ on `principalSeries3` at $\lambda$ — the space of locally constant functions invariant under left translation by the upper unipotent matrices `upperUnipotent3` and transforming under the diagonal torus by $\prod_i\lambda_i(a_i)\cdot\|a_0\|/\|a_2\|$ — where $\Lambda$ is a Whittaker functional for $\psi_p^{-1}$, $\psi_p$ the standard local additive character; moreover $W_2$ itself satisfies $W_2(n(x,y,z)g)=\psi_p^{-1}(x+y)W_2(g)$, is invariant under right translation by some open subgroup, and has central character $\omega_3$. Let $\theta_0$ be a character of $\mathbb Q_p^\times$, $N\neq 0$ an ideal of $\mathcal{O}_{\mathbb Q}$, and $w_2^{\mathrm{base}}:\mathrm{GL}_2(\mathbb Q_p)\to\mathbb C$ a nonzero function with $w_2^{\mathrm{base}}(u(x)g)=\psi_p(x)w_2^{\mathrm{base}}(g)$, invariant under right translation by [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at level $N$, with central character $\theta_0$, and such that the span $V$ of its right translates is irreducible (every nonzero $w\in V$ has $w_2^{\mathrm{base}}$ in the span of the right translates of $w$) and admissible (for each open subgroup $U$ some finite set of functions spans the $U$-right-invariant vectors of $V$). Let $w_0\in\mathrm{GL}_2(\mathbb Q_p)$ be the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Then, for the Borel structure on $\mathrm{GL}_2(\mathbb Q_p)$, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_p)$, every Haar measure $\mu_{N_2}$ on the image of `unipotentGL2Hom`, every $w_2\in V$ and every $W_3$ in the span of the right translates of $W_2$, there are polynomials $P,P^\vee,Q,Q^\vee\in\mathbb C[X]$ with $Q\neq0\neq Q^\vee$, integers $m,m^\vee$ and real abscissae $\sigma_2,\sigma_3$ such that, against $\mu_2$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup: for $\mathrm{Re}\,s>\sigma_2$ the function $g\mapsto W_3(\iota g)\,w_2(g)\,|\det g|^{s-1/2}$ is integrable and the integral `rsLocalIntegral` of $(W_3\circ\iota,w_2)$ at $s$ satisfies $\Psi(s)\cdot Q(q^{-s})=q^{ms}P(q^{-s})$; and for $\mathrm{Re}\,s>\sigma_3$ the function $g\mapsto W_3(w_3\,{}^t(\iota g)^{-1})\cdot|\det g|\,w_2(w_0\,{}^tg^{-1})\cdot|\det g|^{s-1/2}$ is integrable, with $w_3$ the long Weyl element `longWeyl3`, and the corresponding integral $\Psi^\vee(s)$ satisfies $\Psi^\vee(s)\cdot Q^\vee(q^{-s})=q^{m^\vee s}P^\vee(q^{-s})$. Here $\iota$ is the embedding of $\mathrm{GL}_2$ into $\mathrm{GL}_3$ in the upper left block and $|\cdot|$ is the module `modulus` of $\mathbb Q_p$.
--
--   This is the local statement of Jacquet–Piatetski-Shapiro–Shalika for $\mathrm{GL}_3\times\mathrm{GL}_2$ — absolute convergence in a half-plane and rationality in $q^{-s}$ of the local Rankin–Selberg integral and of its dual — specialised to a $\mathrm{GL}_3$ vector coming from a unitary principal series and an arbitrary generic admissible partner on $\mathrm{GL}_2$ of level $K_1(N)$. It supplies the local rationality input to the global functional equation for the $\mathrm{GL}_3\times\mathrm{GL}_2$ convolution used in the cubic-induction construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_principalSeries3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical in

open scoped Classical in

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_principalSeries3
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hlamω : lam 0 * lam 1 * lam 2 = ω₃)
    (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hlamu : ∀ (i : Fin 3) (x : (p.adicCompletion ℚ)ˣ), ‖((lam i x : ℂˣ) : ℂ)‖ = 1)
    (W2 : LocalGL3 p → ℂ)
    (hmem : ∃ (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)),
      IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ ∧ W2 = coefficientFn Λ f)
    (hW2law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W2)
    (hW2sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W2 (g * k) = W2 g)
    (hω2 : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W2 (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W2 h)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W2,
          ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
