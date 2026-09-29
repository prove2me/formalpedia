-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_dominant_rsLocalIntegral_deformedSpherical_eq_and_fe_of_forall_localZeta31_fe_of_gauge
-- name    : LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_dominant_rsLocalIntegral_deformedSpherical_eq_and_fe_of_forall_localZeta31_fe_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/dd015464-494c-5adb-8a05-f34f73c0b602
-- title:
--   Unfolded (3,2) functional equation for deformed spherical vectors
-- statement:
--   Throughout, $v$ is a finite place of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), $N =$ `Ideal.absNorm v.asIdeal` is the absolute norm of $v$, $\mathbb{Q}_v$ denotes `v.adicCompletion ℚ`, and `LocalGL3 v` is $\mathrm{GL}_3(\mathbb{Q}_v)$. The additive character $\psi_v$ on $\mathbb{Q}_v$ is assumed (hypothesis `hψinv`) to be the inverse of the standard local character [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65).
--
--   The $\mathrm{GL}_3$ datum is a function $W : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ subject to the following groups of hypotheses. Whittaker normalisation: `hW` asserts `IsGL3PsiWhittakerFn ψv W`, i.e. $W(u(x,y,z)g) = \psi_v(x+y)W(g)$ for the upper unipotent matrix $u(x,y,z)$ with entries $x,y,z$ above the diagonal, and `hW1` asserts $W(1) = 1$. Multiplicity one: `hmult` asserts `HasWhittakerMultOne ψv W`, i.e. the space of $\psi_v$-Whittaker functionals on the cyclic representation `gl3CyclicRep W` carried by the span `gl3CyclicSubspace W` of the right translates of $W$ has rank at most $1$ over $\mathbb{C}$. Irreducibility: `hirr` asserts that every nonzero $F$ in `gl3CyclicSubspace W` has $W$ in `gl3CyclicSubspace F`. Smoothness: `hsm` asserts the existence of an open subgroup $U_v \le \mathrm{GL}_3(\mathbb{Q}_v)$ with $W(gk) = W(g)$ for all $k \in U_v$ and all $g$. Admissibility: `hadm` asserts that for every open subgroup $U_v$ there is a finite set $B$ of functions such that every $F \in$ `gl3CyclicSubspace W` which is right $U_v$-invariant lies in the $\mathbb{C}$-span of $B$. Gauge majorisation: `hWgauge` asserts the existence of $B \in \mathbb{R}$, $t \in \mathbb{N}$, $C \in \mathbb{R}$ such that, writing $A_1(h) = \mathrm{detSize}(h)\,\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $A_2(h) = \mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$ — where $\mathrm{detSize}(h) = \lVert \det h\rVert$, $\mathrm{lastRowSup}(h)$ is the maximum of the norms of the three entries of the bottom row, and $\mathrm{minorSup}(h)$ is the maximum of the norms of the three $2\times 2$ minors formed from the bottom two rows — one has $W(h) = 0$ whenever it is not the case that $A_1(h) \le B$ and $A_2(h) \le B$, and $\lVert W(h)\rVert \le C/(A_1(h)A_2(h))^t$ whenever $A_1(h) \le B$ and $A_2(h) \le B$. Central character: $\omega_v : \mathbb{Q}_v^{\times} \to \mathbb{C}^{\times}$ is a homomorphism which is unitary (`hωu`: $\lVert \omega_v(z)\rVert = 1$ for all $z$) and satisfies $W(\mathrm{scalar}(t)h) = \omega_v(t)W(h)$ (`hω`). Uniformiser: $\varpi$ is an element of the valuation ring whose image $\pi$ in $\mathbb{Q}_v$ is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`).
--
--   The $(3,1)$ functional-equation data consists of polynomials $E, E^{\vee} \in \mathbb{C}[X]$, a constant $\varepsilon \in \mathbb{C}$ and an integer $\ell \in \mathbb{N}$, subject to the hypothesis `h31`: for every $g \in \mathrm{GL}_3(\mathbb{Q}_v)$ there are a function $P : \mathbb{C} \to \mathbb{C}$ and reals $\sigma_0, \sigma_1$ such that (i) $P$ is rational in $N^{-s}$ up to a monomial, namely there are polynomials $Q, R$ with $R \ne 0$ and an $m \in \mathbb{N}$ with $P(s)R(N^{-s}) = Q(N^{-s})N^{ms}$ for all $s$; (ii) `IsLocalZeta30ConvergentAbove` holds for $W$, the trivial character and $g$ above $\sigma_0$, i.e. for $\mathrm{Re}\,s > \sigma_0$ the integrand $a \mapsto W(\iota(\mathrm{diag}(a,1))g)\,|a|^{s-1}$ is integrable against the multiplicative measure obtained by pulling back `mulMeasure (selfDualHaarAt ℚ v)` along $\mathbb{Q}_v^{\times} \hookrightarrow \mathbb{Q}_v$; (iii) for $\mathrm{Re}\,s > \sigma_0$ the local $(3,1)$-type integral `localZeta30` at $g$ equals $E(N^{-s})^{-1}P(s)$; (iv) `IsLocalZeta31ConvergentAbove` holds for `dualWhittakerFn3 W` (that is, $h \mapsto W(w_3\,{}^t h^{-1})$ for the long Weyl element $w_3$) at the point `weylPrime3 * transposeInv3 g` above $\sigma_1$, the integrability being over $\mathbb{Q}_v^{\times} \times \mathbb{Q}_v$ with the additive factor given by the self-dual Haar measure; and (v) for $\sigma_1 < \mathrm{Re}(1-s)$ the dual integral `localZetaDual31` at $1-s$ and $g$ equals $E^{\vee}(N^{-(1-s)})^{-1}\bigl(\varepsilon N^{\ell(1/2-s)}\bigr)P(s)$.
--
--   The conclusion is the following. Let $a_1, a_2 \in \mathbb{C}$ with $a_1a_2 \ne 0$. Equip $\mathrm{GL}_2(\mathbb{Q}_v)$ with its Borel measurable structure, let $\mu_2$ be a Haar measure on $\mathrm{GL}_2(\mathbb{Q}_v)$ and $\mu_N$ a Haar measure on the range of `unipotentGL2Hom`, i.e. on the upper unipotent subgroup $\{\begin{pmatrix}1&x\\0&1\end{pmatrix}\}$. Then there exist four polynomials $p, q, p^{\vee}, q^{\vee} \in \mathbb{C}[X,Y]$ (elements of `MvPolynomial (Fin 2) ℂ`), depending on $a_1, a_2, \mu_2, \mu_N$ but not on the parameter $u$ nor on the $\mathrm{GL}_2$ Whittaker functions, with the following two properties.
--
--   First, non-degeneracy: for every $y \ne 0$ there is an $x$ with $q(x,y) \ne 0$, and there is an $x$ with $q^{\vee}(x,y) \ne 0$.
--
--   Second, for every $u \in \mathbb{C}$ in the dominant range $\lVert a_1\rVert N^{-\mathrm{Re}\,u} < \lVert a_2\rVert N^{\mathrm{Re}\,u}$, and for all pairs of functions $W_2, W_2^{\vee} : \mathrm{GL}_2(\mathbb{Q}_v) \to \mathbb{C}$ satisfying the unramified-Whittaker conditions for the deformed Satake parameters $\alpha_1 = a_1N^{-u}$, $\alpha_2 = a_2N^{u}$, namely: $W_2(n(x)g) = \psi(x)W_2(g)$ for the standard local character $\psi$ (`hW₂ψ`), right invariance of $W_2$ under the local level-one subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (`hW₂K`), $W_2(1) = 1$ (`hW₂1`), the central relation $W_2(g\,\mathrm{scalar}(\pi)) = \alpha_1\alpha_2 N^{-1}W_2(g)$ (`hW₂Z`), and the torus values $W_2(\mathrm{diag}(\pi^m,1)) = \mathrm{torusFactor}\,N\,(\alpha_1+\alpha_2)\,(\alpha_1\alpha_2 N^{-1})\,m$ for all $m \in \mathbb{Z}$, given by the Hecke recursion (`hW₂T`); and correspondingly for $W_2^{\vee}$ with $\psi$ replaced by $\psi^{-1}$ (`hW₂dψ`), the same level-one invariance (`hW₂dK`), $W_2^{\vee}(1) = 1$ (`hW₂d1`), central relation $W_2^{\vee}(g\,\mathrm{scalar}(\pi)) = N(\alpha_1\alpha_2)^{-1}W_2^{\vee}(g)$ (`hW₂dZ`), and torus values $\mathrm{torusFactor}\,N\,\bigl(N(\alpha_1+\alpha_2)/(\alpha_1\alpha_2)\bigr)\,\bigl(N/(\alpha_1\alpha_2)\bigr)\,m$ (`hW₂dT`) — there exist reals $\sigma_2, \sigma_3$ such that the following five assertions hold, the integrals being taken against $\mu_2$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup with respect to $\mu_N$:
--
--   1.
--
--   for every $s$ with $\mathrm{Re}\,s > \sigma_2$, the function $g \mapsto W(\iota(g))W_2(g)\,|\det g|^{s-1/2}$ is integrable, where $\iota =$ `iotaGL` is the embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$ in the upper-left block and $|\cdot|$ is the local module `modulus`;
--
--   2.
--
--   for every $s$ with $\sigma_3 < \mathrm{Re}(1-s)$, the function $g \mapsto \bigl(\mathrm{dualWhittakerFn3}\,W\bigr)\bigl(\iota(g)\,\iota(\mathrm{scalar}(\pi))^{-\ell}\bigr)W_2^{\vee}(g)\,|\det g|^{(1-s)-1/2}$ is integrable;
--
--   3.
--
--   for every $s$ with $\mathrm{Re}\,s > \sigma_2$, the Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) at $s$ of the pair $\bigl(g \mapsto W(\iota(g)),\,W_2\bigr)$, formed with the weight $g \mapsto |\det g|$, satisfies
--   $$\mathrm{rsLocalIntegral}(s)\cdot q\bigl(N^{-s},N^{u}\bigr) = p\bigl(N^{-s},N^{u}\bigr);$$
--
--   4.
--
--   for every $s$ with $\sigma_3 < \mathrm{Re}(1-s)$, the Rankin–Selberg integral at $1-s$ of the dual pair $\bigl(g \mapsto (\mathrm{dualWhittakerFn3}\,W)(\iota(g)\,\iota(\mathrm{scalar}(\pi))^{-\ell}),\,W_2^{\vee}\bigr)$ satisfies
--   $$\mathrm{rsLocalIntegral}(1-s)\cdot q^{\vee}\bigl(N^{-(1-s)},N^{u}\bigr) = p^{\vee}\bigl(N^{-(1-s)},N^{u}\bigr);$$
--
--   5.
--
--   for every $s \in \mathbb{C}$ (with no half-plane restriction) the $(3,2)$ functional equation holds as an identity of these polynomial values:
--   $$p^{\vee}\bigl(N^{-(1-s)},N^{u}\bigr)\,q\bigl(N^{-s},N^{u}\bigr)\,E^{\vee}\bigl(\alpha_1^{-1}N^{-(1/2-s)}\bigr)E^{\vee}\bigl(\alpha_2^{-1}N^{-(1/2-s)}\bigr)$$
--   $$= p\bigl(N^{-s},N^{u}\bigr)\,q^{\vee}\bigl(N^{-(1-s)},N^{u}\bigr)\,E\bigl(\alpha_1N^{-(s+1/2)}\bigr)E\bigl(\alpha_2N^{-(s+1/2)}\bigr)\,\varepsilon^{2}.$$
--
--   This is the local $\mathrm{GL}_3 \times \mathrm{GL}_2$ functional equation of Jacquet–Piatetski-Shapiro–Shalika at a finite place, in the form used here: the unfolded Rankin–Selberg integrals of the gauge-majorised $\mathrm{GL}_3$ Whittaker function against the normalised unramified $\mathrm{GL}_2$ Whittaker functions of the deformed Satake parameters $(a_1N^{-u}, a_2N^{u})$ are rational in $N^{-s}$ and $N^{u}$ on the dominant cone, and the $(3,1)$ functional equation with data $(E, E^{\vee}, \varepsilon, \ell)$ propagates to a $(3,2)$ functional equation between those rational forms. It feeds the derivation [`LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge`](thm.html#LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge) within the local analysis supporting the cubic-induction step of the Langlands–Tunnell input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_dominant_rsLocalIntegral_deformedSpherical_eq_and_fe_of_forall_localZeta31_fe_of_gauge.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_dominant_rsLocalIntegral_deformedSpherical_eq_and_fe_of_forall_localZeta31_fe_of_gauge
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
    ∃ (p q pd qd : MvPolynomial (Fin 2) ℂ),
      (∀ y : ℂ, y ≠ 0 →
        (∃ x : ℂ, MvPolynomial.eval ![x, y] q ≠ 0) ∧ (∃ x : ℂ, MvPolynomial.eval ![x, y] qd ≠ 0)) ∧
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
      ∃ σ₂ σ₃ : ℝ,
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
            s (fun g => W (iotaGL g)) W₂ * MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)), ((Ideal.absNorm v.asIdeal : ℂ) ^ u)] q =
          MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)), ((Ideal.absNorm v.asIdeal : ℂ) ^ u)] p) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))), ((Ideal.absNorm v.asIdeal : ℂ) ^ u)] qd =
          MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))), ((Ideal.absNorm v.asIdeal : ℂ) ^ u)] pd) ∧
      (∀ s : ℂ,
        MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))), ((Ideal.absNorm v.asIdeal : ℂ) ^ u)] pd * MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)), ((Ideal.absNorm v.asIdeal : ℂ) ^ u)] q *
            Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                s))) *
            Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                s))) =
          MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)), ((Ideal.absNorm v.asIdeal : ℂ) ^ u)] p * MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))), ((Ideal.absNorm v.asIdeal : ℂ) ^ u)] qd *
            E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            E.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            ε ^ 2) := by sorry
