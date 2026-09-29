-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_principalSeries3_of_forall_torusZeta_fe_multiplicativity3_ed3
-- name    : LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_principalSeries3_of_forall_torusZeta_fe_multiplicativity3_ed3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/e4a12640-4ed9-5882-a55a-8981b839afda
-- title:
--   Multiplicativity of the local GL₃× GL₂ functional equation
-- statement:
--   Throughout, $p$ is a height-one prime of $\mathcal O_{\mathbb Q}$, $F_p = \mathbb Q_p$ denotes the completion `p.adicCompletion ℚ`, $q =$ `Ideal.absNorm p.asIdeal`, and $\psi_p =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) is the standard local additive character; `LocalGL3 p` is $GL_3(F_p)$, and the absolute value is `modulus`, the module of the multiplicative translation. Right translation is written via the spans appearing in the statement: for a function $f$ on $GL_n(F_p)$, the span of $\{g \mapsto f(gh) : h\}$ over $\mathbb C$.
--
--   **The $GL_3$ datum.** Given are monoid homomorphisms $\lambda_0,\lambda_1,\lambda_2,\omega_3 : F_p^\times \to \mathbb C^\times$ with $\lambda_0\lambda_1\lambda_2 = \omega_3$ (`hlamω`) and each $\lambda_i$ locally constant (`hlam`), and a function $W_2 : GL_3(F_p) \to \mathbb C$ subject to four hypotheses: `hmem` asserts that $W_2$ is a matrix coefficient `coefficientFn Λ f` of some $\mathbb C$-linear functional $\Lambda$ on the principal series `principalSeries3 p lam` — the space of locally constant functions on $GL_3(F_p)$ invariant under left translation by the upper unipotent subgroup and transforming under the diagonal torus by $\prod_i \lambda_i(a_i)$ times $\|a_0\|/\|a_2\|$ — for some $f$ in that space, $\Lambda$ being a $\psi_p^{-1}$-Whittaker functional in the sense of `IsWhittakerFunctional3` (right translation of an element of the principal series by `upperUnipotent3 x y z` multiplies $\Lambda$ by $\psi_p^{-1}(x+y)$); `hW2law` asserts `IsGL3PsiWhittakerFn` for $\psi_p^{-1}$, i.e. $W_2(u(x,y,z)g) = \psi_p^{-1}(x+y)W_2(g)$ for all $x,y,z \in F_p$ and all $g$, where $u(x,y,z) =$ `upperUnipotent3 x y z`; `hW2sm` asserts that $W_2$ is invariant under right translation by some open subgroup of $GL_3(F_p)$; and `hω2` asserts that $W_2(\mathrm{diag}(t,t,t)\,h) = \omega_3(t)W_2(h)$ for all $t \in F_p^\times$ and all $h$.
--
--   **The $GL_2$ datum.** Given are a monoid homomorphism $\theta_0 : F_p^\times \to \mathbb C^\times$, a nonzero ideal $N$ of $\mathcal O_{\mathbb Q}$ (`hN`), and a function $w_{2,\mathrm{base}} : GL_2(F_p) \to \mathbb C$ with: `hw₂law`, the $\psi_p$-Whittaker law $w_{2,\mathrm{base}}(u(x)g) = \psi_p(x)\,w_{2,\mathrm{base}}(g)$ for `unipotent x` the upper unipotent matrix with entry $x$; `hw₂K`, invariance under right translation by the local level-one group [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding $GL_2(F_p) \to GL_2(\mathbb A_{\mathbb Q}^{\mathrm f})$ of the finite level-one subgroup of level $N$; `hw₂ne`, $w_{2,\mathrm{base}} \neq 0$; `hw₂irr`, an irreducibility clause: every nonzero $w$ in the right-translation span of $w_{2,\mathrm{base}}$ has $w_{2,\mathrm{base}}$ in its own right-translation span; `hw₂adm`, an admissibility clause: for every open subgroup $U$ of $GL_2(F_p)$ there is a finite set $B$ of functions such that every $w$ in the right-translation span of $w_{2,\mathrm{base}}$ which is invariant under right translation by $U$ lies in the span of $B$; and `hcentral`, the central character law $w_{2,\mathrm{base}}(\mathrm{diag}(z,z)g) = \theta_0(z)\,w_{2,\mathrm{base}}(g)$. Two further elements $w_{0p}, w_J \in GL_2(F_p)$ are given, with underlying matrices $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ respectively (`hw₀p`, `hwJ`).
--
--   **The three twisted $GL_2 \times GL_1$ functional equations.** Given are $E : \mathrm{Fin}\,3 \to \mathbb C$ and $e : \mathrm{Fin}\,3 \to \mathbb Z$, and for each $i \in \{0,1,2\}$ a hypothesis `hfe`$i$ of the following shape, stated for the Borel $\sigma$-algebra `localBorel ℚ p` on $F_p$: for every $w$ in the right-translation span of $w_{2,\mathrm{base}}$ there exist polynomials $P, P^\vee \in \mathbb C[X]$, integers $m, m^\vee$ and reals $\sigma_0, \sigma_1$ such that, with respect to the measure on $F_p^\times$ obtained by pulling back along `Units.val` the multiplicative measure `mulMeasure (selfDualHaarAt ℚ p)` attached to the self-dual additive Haar measure at $p$: (a) for $\mathrm{Re}\,s > \sigma_0$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\lambda_i(y)\,\|y\|^{s-1/2}$ is integrable, and (b) its integral equals $q^{ms}P(q^{-s})$; (c) for $\mathrm{Re}\,s < \sigma_1$ the function $y \mapsto w(\mathrm{diag}(y,1)w_J)\,\lambda_i(y)^{-1}\theta_0(y)^{-1}\|y\|^{1/2-s}$ is integrable, and (d) its integral equals $q^{m^\vee s}P^\vee(q^{-s})$; and (e) for all $s \in \mathbb C$,
--   $$q^{m^\vee s}P^\vee(q^{-s}) = \bigl(E_i\,q^{e_i s}\bigr)\cdot q^{ms}P(q^{-s}),$$
--   so that the $i$-th local $\gamma$-factor is the monomial $E_i q^{e_i s}$. Here $\mathrm{diag}(y,1)$ is `diagOne y`.
--
--   **Conclusion.** With the Borel measurable structure `localGLBorel ℚ p` on $GL_2(F_p)$ and the corresponding Borel space instance, the following holds for every Haar measure $\mu_2$ on $GL_2(F_p)$, every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, i.e. on the upper unipotent subgroup $\{u(x)\}$ of $GL_2(F_p)$, every $w_2$ in the right-translation span of $w_{2,\mathrm{base}}$, every $W_3$ in `gl3CyclicSubspace W2` (the span of the right translates $g \mapsto W_2(gh)$), and all polynomials $P, P^\vee, Q, Q^\vee \in \mathbb C[X]$, integers $m, m^\vee$ and reals $\sigma_2, \sigma_3$ with $Q \neq 0$ and $Q^\vee \neq 0$. Write $\iota : GL_2 \to GL_3$ for `iotaGL`, the embedding $h \mapsto \mathrm{diag}(h,1)$, $\delta(g) = \|\det g\|$, $\widetilde W_3 =$ `dualWhittakerFn3 W₃`, i.e. $g \mapsto W_3(w_3\,{}^t g^{-1})$ with $w_3$ the long Weyl element of $GL_3$, and let the measure on $GL_2(F_p)$ be $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup with respect to $\mu_{N_2}$. Assume:
--
--   — for $\mathrm{Re}\,s > \sigma_2$ the function $g \mapsto W_3(\iota g)\,w_2(g)\,\delta(g)^{s-1/2}$ is integrable for that measure;
--
--   — for $\mathrm{Re}\,s > \sigma_3$ the function $g \mapsto \widetilde W_3(\iota g)\,\bigl(\delta(g)\,w_2(w_{0p}\,{}^t g^{-1})\bigr)\,\delta(g)^{s-1/2}$ is integrable, where ${}^t g^{-1} =$ `transposeInvN (Fin 2) g`;
--
--   — for $\mathrm{Re}\,s > \sigma_2$, the Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) for this measure datum, with the modulus $\delta$, at $s$, of the pair $(g \mapsto W_3(\iota g),\; w_2)$, multiplied by $Q(q^{-s})$, equals $q^{ms}P(q^{-s})$;
--
--   — for $\mathrm{Re}\,s > \sigma_3$, the same integral at $s$ of the pair $\bigl(g \mapsto \widetilde W_3(\iota g),\; g \mapsto \delta(g)\,w_2(w_{0p}\,{}^t g^{-1})\bigr)$, multiplied by $Q^\vee(q^{-s})$, equals $q^{m^\vee s}P^\vee(q^{-s})$.
--
--   Then for every $s \in \mathbb C$,
--   $$1 \cdot \bigl(q^{m^\vee s}P^\vee(q^{-s})\bigr)\,Q(q^{s}) = \Bigl(\theta_0(-1)\,E_0E_1E_2\;q^{-(e_0+e_1+e_2)s}\Bigr)\cdot\bigl(q^{-ms}P(q^{s})\bigr)\,Q^\vee(q^{-s}),$$
--   the left factor $1$ and the constant $\theta_0(-1)E_0E_1E_2$ occurring as the evaluations at $q^{s}$ of the constant polynomials $1$ and `Polynomial.C (θ₀ (-1) * (E 0 * E 1 * E 2))`. Thus the cleared functional equation of the pair holds with the single monomial $\gamma$-factor $\theta_0(-1)\prod_i E_i \cdot q^{-(e_0+e_1+e_2)s}$, the product of the three $GL_2 \times GL_1$ factors times $\theta_0(-1)$.
--
--   This is the local multiplicativity of the $GL_3 \times GL_2$ Rankin–Selberg $\gamma$-factor in the $GL_3$ variable under parabolic induction: for a Whittaker matrix coefficient of a principal series $I(\lambda_0,\lambda_1,\lambda_2)$ paired with a $GL_2$ Whittaker datum of central character $\theta_0$, the $\gamma$-factor is $\theta_0(-1)$ times the product of the three $GL_2 \times GL_1$ factors of the twists by $\lambda_i$, here in the form of an identity between cleared rational expressions in $q^{\pm s}$, valid for every choice of Haar measures and of vectors in the two cyclic spans. It is obtained by expanding the matrix coefficient as a finite combination of Jacquet Whittaker integrals and feeding the resulting linear combinations into a formal clearing lemma; it supplies the local input at $p$ for the global $GL_3 \times GL_2$ functional equation used in the converse-theorem step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_principalSeries3_of_forall_torusZeta_fe_multiplicativity3_ed3.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_principalSeries3_of_forall_torusZeta_fe_multiplicativity3_ed3
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hlamω : lam 0 * lam 1 * lam 2 = ω₃)
    (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
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
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (E : Fin 3 → ℂ) (e : Fin 3 → ℤ)
    (hfe0 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 0 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe1 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe2 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 2 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 2 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 2 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 2 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 2 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 2 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    :

    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W2,
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              ((1 : Polynomial ℂ)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                ((Polynomial.C (((θ₀ (-1) : ℂˣ) : ℂ) * (E 0 * E 1 * E 2))).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(e 0 + e 1 + e 2) : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
