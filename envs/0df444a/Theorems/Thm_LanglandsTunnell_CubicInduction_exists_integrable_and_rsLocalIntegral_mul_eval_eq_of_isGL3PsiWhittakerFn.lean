-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/845d5af9-8afe-5890-b287-66072f60c31b
-- title:
--   Rationality in Nᵥ^{-s} of local GL₃× GL₂ integrals
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $N = \#(\mathcal{O}_{\mathbb{Q}}/v)$ for `Ideal.absNorm v.asIdeal`, and let $\varpi$ be an element of the valuation ring of $\mathbb{Q}_v$ whose image in $\mathbb{Q}_v$ is non-zero and has valuation $\exp(-1)$, i.e. a uniformiser. Let $\psi$ denote the standard local additive character [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65). Let $W : GL_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy $W(u(x,y,z)g) = \psi^{-1}(x+y)\,W(g)$ for all $x,y,z$ and all $g$, where $u(x,y,z)$ runs over the upper unipotent matrices `upperUnipotent3`; assume $W$ is right invariant under some open subgroup of $GL_3(\mathbb{Q}_v)$, and that for every open subgroup $U_v$ there is a finite set $B$ of functions such that every element of the span of the right translates of $W$ which is right $U_v$-invariant lies in the $\mathbb{C}$-span of $B$. Let $\ell$ be a natural number. The assertion is then: for all non-zero complex $a_1,a_2$ with $a_1a_2 \neq 0$, and for all $W_2, W_2^{\vee} : GL_2(\mathbb{Q}_v) \to \mathbb{C}$ with $W_2(u(x)g) = \psi(x)W_2(g)$ and $W_2^{\vee}(u(x)g) = \psi^{-1}(x)W_2^{\vee}(g)$ for the unipotent $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, both right invariant under the local level-one subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) at $v$, both taking the value $1$ at the identity, with $W_2(g\cdot \varpi I) = (a_1a_2/N)W_2(g)$, $W_2^{\vee}(g\cdot \varpi I) = (N/(a_1a_2))W_2^{\vee}(g)$, and torus values $W_2(\mathrm{diag}(\varpi^m,1)) =$ `torusFactor` $N\,(a_1+a_2)\,(a_1a_2/N)\,m$, respectively $W_2^{\vee}(\mathrm{diag}(\varpi^m,1)) =$ `torusFactor` $N\,(N(a_1+a_2)/(a_1a_2))\,(N/(a_1a_2))\,m$ for all $m \in \mathbb{Z}$: for the Borel $\sigma$-algebra on $GL_2(\mathbb{Q}_v)$, every Haar measure $\mu_2$ on $GL_2(\mathbb{Q}_v)$ and every Haar measure $\mu_N$ on the image of `unipotentGL2Hom`, there exist complex polynomials $p,q,p^{\vee},q^{\vee}$ with $q \neq 0$, $q^{\vee} \neq 0$, and reals $\sigma_2,\sigma_3$ such that, with respect to $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_N$: for $\mathrm{Re}\,s > \sigma_2$ the function $g \mapsto W(\iota g)W_2(g)\,|\det g|^{s-1/2}$ is integrable, $|\cdot|$ being `modulus`, and $\iota$ the block embedding `iotaGL` of $GL_2$ into $GL_3$; for $\mathrm{Re}(1-s) > \sigma_3$ the function $g \mapsto W^{\vee}(\iota g \cdot \iota((\varpi I)^{-\ell}))\,W_2^{\vee}(g)\,|\det g|^{1-s-1/2}$ is integrable, where $W^{\vee}(h) = W(w_3\,{}^{t}h^{-1})$ is `dualWhittakerFn3 W`; moreover for $\mathrm{Re}\,s > \sigma_2$ the Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) of $W\circ\iota$ against $W_2$ with $\delta(g) = |\det g|$ at $s$ satisfies $(\text{integral})\cdot q(N^{-s}) = p(N^{-s})$, and for $\mathrm{Re}(1-s) > \sigma_3$ the corresponding integral at $1-s$ of $g \mapsto W^{\vee}(\iota g\cdot\iota((\varpi I)^{-\ell}))$ against $W_2^{\vee}$ satisfies $(\text{integral})\cdot q^{\vee}(N^{-(1-s)}) = p^{\vee}(N^{-(1-s)})$.
--
--   This is the local convergence-and-rationality statement of Rankin–Selberg theory for $GL_3\times GL_2$ at a finite place: the local zeta integral of an admissible Whittaker function on $GL_3(\mathbb{Q}_v)$ against the spherical Whittaker vector of an unramified $GL_2$ datum with Satake parameters $a_1,a_2$ converges in a right half-plane and is a rational function of $N^{-s}$, and likewise for the dual Whittaker function translated by a power of the central uniformiser. It feeds the two results establishing the local functional equation and the rational comparison of the local factors used in the cubic-induction construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

theorem
LanglandsTunnell.CubicInduction.exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ℓ : ℕ) :
    ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
    (hW₂1 : W₂ 1 = 1)
    (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m)
    (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * (a₁ + a₂) / (a₁ * a₂))
        ((Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂)) m),
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    ∃ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 ∧ qd ≠ 0 ∧
      (∀ s : ℂ, σ₂ < s.re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(ℓ : ℤ)))) * W₂d g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₂ < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
          pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) := by sorry
