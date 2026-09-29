-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_godementZeta2_clearedFE_of_forall_torusZeta_fe
-- name    : LanglandsTunnell.RankinSelberg.forall_godementZeta2_clearedFE_of_forall_torusZeta_fe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/0e6b42a4-7427-5176-9bf2-1a065c36c388
-- title:
--   Godement–Jacquet zeta integrals for GL₂: cleared functional equation
-- statement:
--   Fix a height one prime $p$ of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the completion `p.adicCompletion ℚ` and $q =$ `Ideal.absNorm p.asIdeal` for the absolute norm of $p$. All integrals are taken with respect to the Borel $\sigma$-algebras on $F$ and on $GL_2(F)$; $|x| =$ `modulus x` denotes the module of $x \in F$ (the scaling factor of Haar measure under multiplication by $x$), and `selfDualHaarAt ℚ p` the additive Haar measure on $F$ self-dual for the standard local additive character $\psi =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), from which the multiplicative measure on $F^\times$ is obtained as `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))`, i.e. the restriction of $|x|^{-1}$ times additive measure to $F \setminus \{0\}$, pulled back to the units.
--
--   The data are: a homomorphism $\theta_0 : F^\times \to \mathbb C^\times$; a nonzero ideal $N$ of $\mathcal O_{\mathbb Q}$ (hypothesis `hN`); a function $w_2 =$ `w₂base` on $GL_2(F)$ with values in $\mathbb C$; an element $w_J \in GL_2(F)$ whose underlying matrix is $\begin{pmatrix} 0 & 1 \\ -1 & 0\end{pmatrix}$ (`hwJ`); a homomorphism $\chi : F^\times \to \mathbb C^\times$ which is locally constant (`hχ`); a constant $E_0 \in \mathbb C$ and an integer $e_0$. Throughout, $V$ denotes the $\mathbb C$-span of the right translates $g \mapsto w_2(gh)$, $h \in GL_2(F)$.
--
--   The hypotheses on $w_2$ are: `hw₂law`, the Whittaker transformation law $w_2\bigl(\begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix} g\bigr) = \psi(x)\, w_2(g)$ for all $x \in F$ and $g \in GL_2(F)$; `hw₂K`, right invariance $w_2(gk) = w_2(g)$ for all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the embedding $GL_2(F) \to GL_2(\mathbb A_{\mathbb Q,\mathrm{fin}})$ of the adelic level-$N$ subgroup `AdelicLevel.finiteLevelOne`; `hw₂ne`, $w_2 \neq 0$; `hw₂irr`, an irreducibility clause asserting that for every $w \in V$ with $w \neq 0$ the function $w_2$ itself lies in the span of the right translates of $w$; `hw₂adm`, an admissibility clause asserting that for every open subgroup $U \le GL_2(F)$ there is a finite set $B$ of functions on $GL_2(F)$ such that every $w \in V$ satisfying $w(gk) = w(g)$ for all $k \in U$, $g \in GL_2(F)$ lies in the span of $B$; and `hcentral`, the central character law $w_2(z \cdot g) = \theta_0(z)\, w_2(g)$ for scalar matrices $z \in F^\times$.
--
--   The hypothesis `hfe` is the torus-zeta functional equation for the whole of $V$: for every $w \in V$ there are polynomials $P, P^\vee \in \mathbb C[X]$, integers $m, m^\vee$ and reals $\sigma_0, \sigma_1$ such that, with `diagOne y` $= \mathrm{diag}(y,1)$, (i) for $\operatorname{Re} s > \sigma_0$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\chi(y)\,|y|^{s-1/2}$ is integrable on $F^\times$ and (ii) its integral equals $q^{m s} P(q^{-s})$; (iii) for $\operatorname{Re} s < \sigma_1$ the function $y \mapsto w(\mathrm{diag}(y,1)\,w_J)\,\chi(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is integrable on $F^\times$ and (iv) its integral equals $q^{m^\vee s} P^\vee(q^{-s})$; and (v) for all $s \in \mathbb C$,
--   $$q^{m^\vee s} P^\vee(q^{-s}) = \bigl(E_0\, q^{e_0 s}\bigr)\cdot q^{m s} P(q^{-s}).$$
--
--   Conclusion. For every Haar measure $\mu_2$ on $GL_2(F)$, every $w \in V$, every $\mathbb C$-linear functional $\ell$ on the space of all functions $GL_2(F) \to \mathbb C$ which is smooth on $V$ in the sense that there is an open subgroup $U \le GL_2(F)$ with $\ell\bigl(g \mapsto v(gk)\bigr) = \ell(v)$ for all $k \in U$ and all $v \in V$, and every locally constant, compactly supported $\Phi : M_2(F) \to \mathbb C$, there exist polynomials $P, P^\vee, Q, Q^\vee \in \mathbb C[X]$, integers $m, m^\vee$ and reals $\sigma_2, \sigma_3$ with $Q \neq 0$ and $Q^\vee \neq 0$ such that the following five assertions hold. Write $c(g) = \ell\bigl(x \mapsto w(xg)\bigr)$ for the matrix coefficient attached to $w$ and $\ell$, $c^{\iota}(g) = \ell\bigl(x \mapsto w(x \cdot {}^{t}(g^{-1}))\bigr)$ for its twist by `transposeInvN`, and $\widehat\Phi =$ `matFourier22 p` $\psi$ $\Phi$ for the iterated column Fourier transform of $\Phi$ (the transform `colFourier22` in the first column of the transform in the second column, taken against $\psi$ and the self-dual measure).
--
--   First, for $\operatorname{Re} s > \sigma_2$ the function $g \mapsto c(g)\,\Phi(g)\,\chi(\det g)\,|\det g|^{s+1/2}$ is $\mu_2$-integrable. Secondly, for $\operatorname{Re} s > \sigma_2$,
--   $$Z\bigl(c, \Phi, \chi; s + \tfrac12\bigr) \cdot Q(q^{-s}) = q^{m s}\, P(q^{-s}),$$
--   where $Z(c,\Phi,\chi;\sigma) =$ `godementZeta2 p μ₂ c Φ χ σ` is the integral over $GL_2(F)$ of $c(g)\,\Phi(g)\,\chi(\det g)\,|\det g|^{\sigma}$ against $\mu_2$. Thirdly, for $\operatorname{Re} s > \sigma_3$ the function $g \mapsto c^{\iota}(g)\,\widehat\Phi(g)\,\chi^{-1}(\det g)\,|\det g|^{s+3/2}$ is $\mu_2$-integrable. Fourthly, for $\operatorname{Re} s > \sigma_3$,
--   $$Z\bigl(c^{\iota}, \widehat\Phi, \chi^{-1}; s + \tfrac32\bigr)\cdot Q^\vee(q^{-s}) = q^{m^\vee s}\, P^\vee(q^{-s}).$$
--   Fifthly, as an identity of functions of $s$ valid for all $s \in \mathbb C$,
--   $$1 \cdot \bigl(q^{m^\vee s} P^\vee(q^{-s})\bigr)\, Q(q^{s}) = \bigl(E_0 \, q^{-e_0 s}\bigr)\cdot \bigl(q^{-m s} P(q^{s})\bigr)\cdot Q^\vee(q^{-s}),$$
--   the leading factor being the evaluation of the constant polynomial $1$ at $q^{s}$ and $E_0$ the evaluation of `Polynomial.C E₀` at $q^{s}$.
--
--   Thus the two Godement–Jacquet zeta integrals, after multiplication by the nonzero denominators $Q$, $Q^\vee$ evaluated at $q^{-s}$, are given by monomials times polynomials in $q^{-s}$ on right half-planes, and these rational expressions are linked by the functional equation with the same constant $E_0$ and exponent $e_0$ as in the torus-zeta hypothesis, with $s$ and $-s$ interchanged.
--
--   This is the local Godement–Jacquet theory for $GL_2$ at a finite place, in the form needed later: rationality in $q^{-s}$ of the zeta integral of a matrix coefficient of a generic irreducible admissible representation against a Schwartz–Bruhat function on $M_2(F)$, together with the functional equation relating it to the integral for the Fourier-transformed datum, the $\gamma$-factor being transported from the $GL_2 \times GL_1$ torus-zeta functional equation assumed in `hfe`. It is used in the Rankin–Selberg input to the converse theorem, via [`LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core_of_chamber`](thm.html#LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core_of_chamber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_godementZeta2_clearedFE_of_forall_torusZeta_fe.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.forall_godementZeta2_clearedFE_of_forall_torusZeta_fe
    (p : HeightOneSpectrum (𝓞 ℚ))

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
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (E₀ : ℂ) (e₀ : ℤ)
    (hfe : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    :

    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (ℓ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ),
          (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
            ∀ k ∈ U, ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
              ℓ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * k)) = ℓ v) →
          ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
            ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

              (∀ s : ℂ, σ₂ < s.re →
                Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * g)) * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) ∧

              (∀ s : ℂ, σ₂ < s.re →
                godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * g))) Φ χ (s + 1 / 2) *
                    Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                  (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

              (∀ s : ℂ, σ₃ < s.re →
                Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * transposeInvN (Fin 2) g)) *
                    matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                    ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) ∧

              (∀ s : ℂ, σ₃ < s.re →
                godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * transposeInvN (Fin 2) g)))
                    (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ)
                    χ⁻¹ (s + 3 / 2) *
                    Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                  (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

              (∀ s : ℂ,
                ((1 : Polynomial ℂ)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                    ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                    Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                  ((Polynomial.C E₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-e₀ : ℤ) : ℂ) * s)) *
                    ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                    Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
