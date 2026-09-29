-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge
-- name    : LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b4f90781-dcc9-54b4-b230-05a8f2b3ad8d
-- title:
--   Common middle of the local GL₃timesGL₂ functional equation
-- statement:
--   Throughout, $v$ is a height-one prime of $\mathcal O_{\mathbb Q}$, $N=\operatorname{absNorm}(v)$ denotes the absolute norm of the corresponding ideal, $\mathbb Q_v$ the $v$-adic completion, and `LocalGL3 v` abbreviates $\mathrm{GL}_3(\mathbb Q_v)$. An additive character $\psi_v$ of $\mathbb Q_v$ is given, together with the hypothesis `hψinv` identifying it with the inverse $(\mathrm{psiLocal}\ \mathbb Q\ v)^{-1}$ of the standard local character at $v$. An element $\varpi$ of the valuation ring is given whose image in $\mathbb Q_v$ is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`), i.e. is a uniformiser.
--
--   The function $W:\mathrm{GL}_3(\mathbb Q_v)\to\mathbb C$ carries the following hypotheses. `hW` asserts `IsGL3PsiWhittakerFn ψv W`, that is, $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z\in\mathbb Q_v$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x$ in position $(0,1)$, $y$ in $(1,2)$ and $z$ in $(0,2)$; `hW1` is $W(1)=1$. `hmult` asserts `HasWhittakerMultOne ψv W`: the space of $\psi_v$-Whittaker functionals on the right-translation representation `gl3CyclicRep W` on the span `gl3CyclicSubspace W` of the right translates of $W$ has $\mathbb C$-rank at most $1$. `hirr` asks that every nonzero $F$ in `gl3CyclicSubspace W` have $W$ in `gl3CyclicSubspace F`. `hsm` (smoothness) provides an open subgroup $U_v\le\mathrm{GL}_3(\mathbb Q_v)$ with $W(gk)=W(g)$ for $k\in U_v$; `hadm` (admissibility) requires that for every open subgroup $U_v$ there be a finite set $B$ of functions such that every $F\in$ `gl3CyclicSubspace W` which is right $U_v$-invariant lies in the $\mathbb C$-span of $B$. `hWgauge` is a majorisation hypothesis in terms of the two gauge quantities
--   $$A_1(h)=\frac{\mathrm{detSize}(h)\,\mathrm{lastRowSup}(h)}{\mathrm{minorSup}(h)^2},\qquad A_2(h)=\frac{\mathrm{minorSup}(h)}{\mathrm{lastRowSup}(h)^2},$$
--   where $\mathrm{detSize}(h)=\lVert\det h\rVert$, $\mathrm{lastRowSup}(h)$ is the maximum of the norms of the three entries of the last row of $h$, and $\mathrm{minorSup}(h)$ is the maximum of the norms of the three $2\times2$ minors formed from rows $1$ and $2$ of $h$: there are $B\in\mathbb R$, $t\in\mathbb N$, $C\in\mathbb R$ such that for every $h$, if not both $A_1(h)\le B$ and $A_2(h)\le B$ then $W(h)=0$, while if both hold then $\lVert W(h)\rVert\le C/(A_1(h)A_2(h))^t$. Finally, $\omega_v:\mathbb Q_v^\times\to\mathbb C^\times$ is a character with $\lvert\omega_v(z)\rvert=1$ for all $z$ (`hωu`) which acts as the central character of $W$: $W(\mathrm{scalar}(t)h)=\omega_v(t)W(h)$ (`hω`).
--
--   Polynomials $E,E^\vee\in\mathbb C[X]$, a constant $\varepsilon\in\mathbb C$ and $\ell\in\mathbb N$ are given, subject to the translate-wise $(3,1)$ functional equation `h31`: for every $g\in\mathrm{GL}_3(\mathbb Q_v)$ there are a function $P:\mathbb C\to\mathbb C$ and real abscissae $\sigma_0,\sigma_1$ such that (i) there are polynomials $Q,R$ with $R\neq0$ and an $m\in\mathbb N$ with $P(s)R(N^{-s})=Q(N^{-s})N^{ms}$ for all $s$; (ii) the integrand of `localZeta30` for $W$, the trivial character and the point $g$ is integrable for $\mathrm{Re}\,s>\sigma_0$ with respect to the multiplicative measure obtained by pulling back `mulMeasure (selfDualHaarAt ℚ v)` along $\mathbb Q_v^\times\to\mathbb Q_v$; (iii) for $\mathrm{Re}\,s>\sigma_0$ one has $\mathrm{localZeta30}(s,g)=E(N^{-s})^{-1}P(s)$; (iv) the analogous $(3,1)$ integrand for `dualWhittakerFn3 W`, the trivial character and the point $w'\,{}^{t}g^{-1}$ (with $w'$ the permutation matrix interchanging the last two coordinates and ${}^{t}g^{-1}$ the transpose inverse) is integrable above $\sigma_1$ with respect to that multiplicative measure and `selfDualHaarAt ℚ v`; and (v) for $\mathrm{Re}(1-s)>\sigma_1$,
--   $$\mathrm{localZetaDual31}(1-s,g)=E^\vee\bigl(N^{-(1-s)}\bigr)^{-1}\bigl(\varepsilon\,N^{\ell(1/2-s)}\bigr)P(s),$$
--   where `localZetaDual31` at $(1-s,g)$ is by definition `localZeta31` for `dualWhittakerFn3 W`, the inverse character, and the point $w'\,{}^{t}g^{-1}$.
--
--   The conclusion is universally quantified over the following further data: complex numbers $a_1,a_2$ with $a_1a_2\neq0$; a Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_v)$ (with its Borel structure) and a Haar measure $\mu_N$ on the range of `unipotentGL2Hom`, the subgroup of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$; a parameter $u\in\mathbb C$ in the dominant range $\lVert a_1\rVert N^{-\mathrm{Re}\,u}<\lVert a_2\rVert N^{\mathrm{Re}\,u}$; and a pair of functions $W_2,W_2^\vee$ on $\mathrm{GL}_2(\mathbb Q_v)$. Writing $\alpha_1=a_1N^{-u}$ and $\alpha_2=a_2N^{u}$, the conditions on $W_2$ are: left equivariance $W_2(n(x)g)=\mathrm{psiLocal}(x)W_2(g)$ for the standard character (`hW₂ψ`); right invariance under the level-one subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding of the finite level-one subgroup for the unit ideal (`hW₂K`); $W_2(1)=1$ (`hW₂1`); the centre law $W_2\bigl(g\cdot\mathrm{diag}(\varpi,\varpi)\bigr)=\bigl(\alpha_1\alpha_2/N\bigr)W_2(g)$ (`hW₂Z`); and the torus law $W_2\bigl(\mathrm{diag}(\varpi^m,1)\bigr)=\mathrm{torusFactor}\,N\,(\alpha_1+\alpha_2)\,(\alpha_1\alpha_2/N)\,m$ for all $m\in\mathbb Z$ (`hW₂T`), where `torusFactor` vanishes for $m<0$ and for $m\ge0$ is the value at $m$ of the Hecke recursion with $x_0=1$, $x_1=\lambda/N$, $x_{m+2}=(\lambda x_{m+1}-\omega x_m)/N$. The conditions on $W_2^\vee$ are the mirror ones: left $(\mathrm{psiLocal})^{-1}$-equivariance (`hW₂dψ`), the same right level-one invariance (`hW₂dK`), $W_2^\vee(1)=1$ (`hW₂d1`), the centre law with factor $N/(\alpha_1\alpha_2)$ (`hW₂dZ`), and the torus law with parameters $\mathrm{torusFactor}\,N\,\bigl(N(\alpha_1+\alpha_2)/(\alpha_1\alpha_2)\bigr)\,\bigl(N/(\alpha_1\alpha_2)\bigr)$ (`hW₂dT`).
--
--   Under these hypotheses there exist polynomials $m_1,m_2\in\mathbb C[X]$ with $m_2\neq0$, an integer $k$, and real numbers $\sigma_P,\sigma_D$ such that the following two assertions hold, where [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) with the modulus function $g\mapsto\mathrm{modulus}(\det g)$ denotes the integral of $(\text{first function})(g)\cdot(\text{second function})(g)\cdot\lvert\det g\rvert^{s-1/2}$ against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_N$.
--
--   First, for every $s$ with $\mathrm{Re}\,s>\sigma_P$, the integral at $s$ of the pair $\bigl(g\mapsto W(\iota g),\,W_2\bigr)$, where $\iota=\mathrm{iotaGL}$ sends $g\in\mathrm{GL}_2$ to the block matrix $\mathrm{diag}(g,1)$, satisfies
--   $$\Psi(s)\;E\bigl(\alpha_1N^{-(s+1/2)}\bigr)\,E\bigl(\alpha_2N^{-(s+1/2)}\bigr)\,m_2(N^{-s})=m_1(N^{-s})\,N^{ks}.$$
--
--   Secondly, for every $s$ with $\mathrm{Re}(1-s)>\sigma_D$, the integral at $1-s$ of the pair $\bigl(g\mapsto \mathrm{dualWhittakerFn3}\,W\,(\iota g\cdot\iota(\mathrm{diag}(\varpi,\varpi)^{-\ell})),\,W_2^\vee\bigr)$, with $\mathrm{dualWhittakerFn3}\,W\,(h)=W(w_0\,{}^{t}h^{-1})$ for $w_0$ the long Weyl element of $\mathrm{GL}_3$, satisfies
--   $$\widetilde\Psi(1-s)\;E^\vee\bigl(\alpha_1^{-1}N^{-(1/2-s)}\bigr)\,E^\vee\bigl(\alpha_2^{-1}N^{-(1/2-s)}\bigr)\,m_2(N^{-s})=\varepsilon^2\bigl(m_1(N^{-s})\,N^{ks}\bigr).$$
--
--   The same triple $(m_1,m_2,k)$ occurs in both clauses; no assertion of convergence, and no comparison of the two integrals outside their respective half-planes, is part of the statement.
--
--   This is the common-middle step of the local $\mathrm{GL}_3\times\mathrm{GL}_2$ functional equation of Jacquet, Piatetski-Shapiro and Shalika, in the form needed on the rational torus: after multiplication by the relevant Euler factors, the unfolded primal integral on its half-plane and the unfolded dual integral on its half-plane are cleared forms of one and the same rational function $m_1(N^{-s})N^{ks}/m_2(N^{-s})$ of $N^{-s}$, the dual one up to the factor $\varepsilon^2$. It feeds [`LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_dominant_rsLocalIntegral_deformedSpherical_eq_and_fe_of_forall_localZeta31_fe_of_gauge`](thm.html#LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_dominant_rsLocalIntegral_deformedSpherical_eq_and_fe_of_forall_localZeta31_fe_of_gauge), where the dependence on the deformation parameter is packaged polynomially.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))) :
    ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0),
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∀ u : ℂ, ‖a₁‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-u.re) < ‖a₂‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u.re →
      ∀ (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
    (hW₂1 : W₂ 1 = 1)
    (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) + (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) / (Ideal.absNorm v.asIdeal : ℂ)) m)
    (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) + (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)))
        ((Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u))) m),
      ∃ (m₁ m₂ : Polynomial ℂ) (k : ℤ) (σP σD : ℝ), m₂ ≠ 0 ∧
      (∀ s : ℂ, σP < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂ *
            E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            E.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            m₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          m₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℂ) * s)) ∧
      (∀ s : ℂ, σD < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
            Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
            m₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          ε ^ 2 * (m₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℂ) * s))) := by sorry
