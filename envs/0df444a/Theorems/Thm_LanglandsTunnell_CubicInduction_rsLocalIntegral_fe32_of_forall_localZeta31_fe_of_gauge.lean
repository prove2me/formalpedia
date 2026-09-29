-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
-- name    : LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/bb818aa8-5bcc-5d78-b42c-a265ae51df5e
-- title:
--   Multiplicativity of the local GL₃timesGL₂ functional equation, unramified partner
-- statement:
--   Throughout, $v$ is a finite place of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), $N = \mathrm{absNorm}(v)$ is the absolute norm of the corresponding prime ideal, and $\mathbb{Q}_v$ denotes `v.adicCompletion ℚ`. The additive character $\psi_v$ of $\mathbb{Q}_v$ is required by `hψinv` to be the inverse of the standard local character [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65). Two measures occur on the $\mathrm{GL}_3$ side: the multiplicative measure on $\mathbb{Q}_v^\times$ obtained by pulling back along the inclusion of units the measure `mulMeasure (selfDualHaarAt ℚ v)`, i.e. the self-dual additive Haar measure on $\mathbb{Q}_v$ restricted to $\{0\}^{c}$ and weighted by $\mathrm{modulus}(x)^{-1}$, and the self-dual additive measure `selfDualHaarAt ℚ v` itself; here $\mathrm{modulus}(a)$ is the module of $a$, defined as the distributive Haar character of $a$ for $a \neq 0$ and as $0$ for $a = 0$.
--
--   The $\mathrm{GL}_3$ datum is a function $W : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ subject to the following groups of hypotheses. *Whittaker normalisation*: `hW` says that $W(u(x,y,z)g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x$ in position $(0,1)$, $y$ in position $(1,2)$ and $z$ in position $(0,2)$; and `hW1` normalises $W(1) = 1$. *Representation-theoretic hypotheses*: writing $\mathrm{gl3CyclicSubspace}\,W$ for the $\mathbb{C}$-span of the right translates $h \mapsto W(hg)$ of $W$, the hypothesis `hmult` is `HasWhittakerMultOne ψv W`, i.e. `GL3WhittakerUniquenessStatement` for the right-translation representation `gl3CyclicRep W` of $\mathrm{GL}_3(\mathbb{Q}_v)$ on that span: the space `gl3WhittakerFunctionalSpace` of $\psi_v$-Whittaker functionals on it has rank at most $1$ over $\mathbb{C}$; `hirr` requires that every non-zero $F$ in that span has $W$ in the span of its own right translates; `hsm` requires an open subgroup $U_v \le \mathrm{GL}_3(\mathbb{Q}_v)$ with $W(gk) = W(g)$ for $k \in U_v$; and `hadm` requires that for every open subgroup $U_v$ there be a finite set $B$ of functions such that each member of $\mathrm{gl3CyclicSubspace}\,W$ that is right $U_v$-invariant lies in the $\mathbb{C}$-span of $B$. *Gauge majorisation* `hWgauge`: there are $B, C \in \mathbb{R}$ and $t \in \mathbb{N}$ such that, setting for $h \in \mathrm{GL}_3(\mathbb{Q}_v)$
--   $$A_1(h) = \frac{\mathrm{detSize}(h)\cdot \mathrm{lastRowSup}(h)}{\mathrm{minorSup}(h)^2}, \qquad A_2(h) = \frac{\mathrm{minorSup}(h)}{\mathrm{lastRowSup}(h)^2},$$
--   where $\mathrm{detSize}(h) = \lVert \det h\rVert$, $\mathrm{lastRowSup}(h)$ is the maximum of the norms of the three entries of the bottom row of $h$, and $\mathrm{minorSup}(h)$ is the maximum of the norms of the three $2\times 2$ minors of $h$ formed from its last two rows, one has $W(h) = 0$ whenever the conjunction $A_1(h) \le B \wedge A_2(h) \le B$ fails, and $\lVert W(h)\rVert \le C/(A_1(h)A_2(h))^t$ whenever it holds. *Central behaviour*: $\omega_v : \mathbb{Q}_v^\times \to \mathbb{C}^\times$ is a homomorphism with $\lVert \omega_v(z)\rVert = 1$ for all $z$ (`hωu`) and $W(\mathrm{scalar}(t)\,h) = \omega_v(t) W(h)$ (`hω`). *Uniformiser*: $\varpi$ is an element of the ring of integers of $\mathbb{Q}_v$ whose image in $\mathbb{Q}_v$ is non-zero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`).
--
--   Finally, polynomials $E, E^{\vee} \in \mathbb{C}[X]$ (named `E` and `Ed`), a scalar $\varepsilon \in \mathbb{C}$ and an integer $\ell \in \mathbb{N}$ are fixed, and the hypothesis `h31` provides the $\mathrm{GL}_3 \times \mathrm{GL}_1$ functional equation in the following form: for every $g \in \mathrm{GL}_3(\mathbb{Q}_v)$ there exist a function $P : \mathbb{C} \to \mathbb{C}$ and reals $\sigma_0, \sigma_1$ such that (i) $P$ is rational in $N^{-s}$ up to a monomial, that is, there are polynomials $Q, R$ with $R \neq 0$ and an $m \in \mathbb{N}$ with $P(s)R(N^{-s}) = Q(N^{-s})N^{ms}$ for all $s$; (ii) `IsLocalZeta30ConvergentAbove` holds for $W$, the trivial character and the point $g$ with abscissa $\sigma_0$, i.e. for $\mathrm{Re}\,s > \sigma_0$ the function $a \mapsto W(\iota(\mathrm{diag}(a,1))g)\,\mathrm{modulus}(a)^{s-1}$ is integrable on $\mathbb{Q}_v^\times$, where $\iota$ is the embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$ in the upper left corner; (iii) for $\mathrm{Re}\,s > \sigma_0$ the integral $\mathrm{localZeta30}$ of that function equals $E(N^{-s})^{-1}P(s)$; (iv) `IsLocalZeta31ConvergentAbove` holds for the dual function $\mathrm{dualWhittakerFn3}\,W : h \mapsto W(w_{\mathrm{long}}\,{}^{t}h^{-1})$, the trivial character and the point $w'\,{}^{t}g^{-1}$ with abscissa $\sigma_1$, where $w_{\mathrm{long}}$ is the antidiagonal permutation matrix and $w'$ the permutation matrix interchanging the last two coordinates: for $\mathrm{Re}\,s > \sigma_1$ the function $(a,x) \mapsto \mathrm{dualWhittakerFn3}\,W(\iota(\mathrm{diag}(a,1))\,n^{-}(x)\,w'\,{}^{t}g^{-1})\,\mathrm{modulus}(a)^{s-1}$ is integrable on the product of $\mathbb{Q}_v^\times$ and $\mathbb{Q}_v$, with $n^{-}(x)$ the lower unipotent matrix having $x$ in position $(1,0)$; and (v) for every $s$ with $\sigma_1 < \mathrm{Re}(1-s)$,
--   $$\mathrm{localZetaDual31}(W, 1, 1-s, g) = E^{\vee}\bigl(N^{-(1-s)}\bigr)^{-1}\bigl(\varepsilon\, N^{\ell(1/2-s)} P(s)\bigr),$$
--   where $\mathrm{localZetaDual31}$ at $1-s$ and $g$ is by definition the double integral $\mathrm{localZeta31}$ of $\mathrm{dualWhittakerFn3}\,W$ against the inverse of the trivial character at the point $w'\,{}^{t}g^{-1}$.
--
--   The conclusion is an assertion for all Satake data and all spherical $\mathrm{GL}_2$ Whittaker pairs. Let $a_1, a_2 \in \mathbb{C}$ with $a_1 a_2 \neq 0$. Let $W_2 : \mathrm{GL}_2(\mathbb{Q}_v) \to \mathbb{C}$ satisfy: $W_2(u(x)g) = \psi^{\mathrm{std}}_v(x)W_2(g)$ for the standard character `psiLocal` and the unipotent $u(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ (`hW₂ψ`); right invariance $W_2(gk) = W_2(g)$ for $k$ in the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the local embedding `localEmbed` of the finite-adelic level-one subgroup at the unit ideal (`hW₂K`); $W_2(1) = 1$; $W_2(g\,\mathrm{scalar}(\varpi)) = (a_1a_2/N)W_2(g)$ (`hW₂Z`); and $W_2(\mathrm{diag}(\varpi^m,1)) = \mathrm{torusFactor}(N, a_1+a_2, a_1a_2/N, m)$ for all $m \in \mathbb{Z}$ (`hW₂T`), where $\mathrm{torusFactor}(N,\lambda,\omega,m)$ is $0$ for $m < 0$ and otherwise the $m$-th term of the recursion $x_0 = 1$, $x_1 = \lambda/N$, $x_{k+2} = (\lambda x_{k+1} - \omega x_k)/N$. Let $W_2^{\vee}$ satisfy the same four conditions with $\psi^{\mathrm{std}}_v$ replaced by its inverse (`hW₂dψ`), the same level-one invariance (`hW₂dK`), $W_2^{\vee}(1) = 1$, $W_2^{\vee}(g\,\mathrm{scalar}(\varpi)) = (N/(a_1a_2))W_2^{\vee}(g)$, and $W_2^{\vee}(\mathrm{diag}(\varpi^m,1)) = \mathrm{torusFactor}(N, N(a_1+a_2)/(a_1a_2), N/(a_1a_2), m)$.
--
--   With $\mathrm{GL}_2(\mathbb{Q}_v)$ given its Borel $\sigma$-algebra, let $\mu_2$ be a Haar measure on $\mathrm{GL}_2(\mathbb{Q}_v)$ and $\mu_N$ a Haar measure on the range of `unipotentGL2Hom`, the unipotent subgroup $\{u(x)\}$; write $\mu$ for $\mu_2$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of that subgroup with respect to $\mu_N$, and $\delta(g) = \mathrm{modulus}(\det g)$. Then there exist polynomials $p, q, p^{\vee}, q^{\vee} \in \mathbb{C}[X]$ and reals $\sigma_2, \sigma_3$ with $q \neq 0$, $q^{\vee} \neq 0$ such that the following five statements hold.
--
--   First, for every $s$ with $\mathrm{Re}\,s > \sigma_2$ the function $g \mapsto W(\iota(g))W_2(g)\,\delta(g)^{s-1/2}$ is integrable with respect to $\mu$. Second, for every $s$ with $\sigma_3 < \mathrm{Re}(1-s)$ the function
--   $$g \mapsto \mathrm{dualWhittakerFn3}\,W\bigl(\iota(g)\,\iota(\mathrm{scalar}(\varpi)^{-\ell})\bigr)\,W_2^{\vee}(g)\,\delta(g)^{1-s-1/2}$$
--   is integrable with respect to $\mu$. Third, for every $s$ with $\mathrm{Re}\,s > \sigma_2$,
--   $$\mathrm{rsLocalIntegral}\bigl(\mu_2, N_{\mathrm{unip}}, \mu_N, \delta, s, g \mapsto W(\iota(g)), W_2\bigr)\cdot q(N^{-s}) = p(N^{-s}),$$
--   where $\mathrm{rsLocalIntegral}$ denotes $\int (W(\iota(g))W_2(g))\,\delta(g)^{s-1/2}\,d\mu$. Fourth, for every $s$ with $\sigma_3 < \mathrm{Re}(1-s)$,
--   $$\mathrm{rsLocalIntegral}\bigl(\mu_2, N_{\mathrm{unip}}, \mu_N, \delta, 1-s, g \mapsto \mathrm{dualWhittakerFn3}\,W(\iota(g)\iota(\mathrm{scalar}(\varpi)^{-\ell})), W_2^{\vee}\bigr)\cdot q^{\vee}\bigl(N^{-(1-s)}\bigr) = p^{\vee}\bigl(N^{-(1-s)}\bigr).$$
--   Fifth, for every $s \in \mathbb{C}$,
--   $$p^{\vee}\bigl(N^{-(1-s)}\bigr)\,q(N^{-s})\,E^{\vee}\bigl(a_1^{-1}N^{-(1/2-s)}\bigr)\,E^{\vee}\bigl(a_2^{-1}N^{-(1/2-s)}\bigr) = p(N^{-s})\,q^{\vee}\bigl(N^{-(1-s)}\bigr)\,E\bigl(a_1N^{-(s+1/2)}\bigr)\,E\bigl(a_2N^{-(s+1/2)}\bigr)\,\varepsilon^{2}.$$
--
--   Thus the $\mathrm{GL}_3 \times \mathrm{GL}_2$ Rankin–Selberg integrals against the spherical pair $(W_2, W_2^{\vee})$ with Satake parameters $a_1, a_2$ are rational in $N^{-s}$ on the respective half-planes, and their ratio satisfies the functional equation obtained by multiplying the two $\mathrm{GL}_3 \times \mathrm{GL}_1$ functional equations with shifted parameters, the $\varepsilon$-factor appearing squared.
--
--   This is the local multiplicativity of the $\mathrm{GL}_3 \times \mathrm{GL}_2$ gamma factor in the $\mathrm{GL}_2$ variable at a finite place, in the case of an unramified (spherical) $\mathrm{GL}_2$ partner with Satake parameters $a_1, a_2$: the $\mathrm{GL}_3\times\mathrm{GL}_1$ functional equation with local factors $E$, $E^{\vee}$, $\varepsilon$ and shift $\ell$ is transported to a functional equation for the $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg integrals, in the style of Jacquet–Piatetski-Shapiro–Shalika, with an added gauge majorisation of $W$ supplying absolute convergence. It is proved by combining a convergence-and-rationality statement for the local integrals with the functional equation for their rational forms, and feeds the version of the result stated for all members of the cyclic span of $W$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge.lean

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

theorem
LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
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
          pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) ∧
      (∀ s : ℂ,
        pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            Ed.eval (a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                s))) *
            Ed.eval (a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                s))) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) *
            E.eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            E.eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            ε ^ 2) := by sorry
