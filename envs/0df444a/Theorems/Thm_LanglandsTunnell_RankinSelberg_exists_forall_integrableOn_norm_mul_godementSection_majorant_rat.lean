-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrableOn_norm_mul_godementSection_majorant_rat
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrableOn_norm_mul_godementSection_majorant_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/5bb59e07-916b-5a3c-95e5-1e2e385d3ca7
-- title:
--   Integrability of the folded Rankin–Selberg integrand over ℚ
-- statement:
--   Throughout, $\mathbb{A}=\mathbb{A}_{\mathbb Q}$ denotes the adele ring of $\mathbb Q$, $\mathrm{AdelicGL2}\,(\mathcal O_{\mathbb Q})\,\mathbb Q = \mathrm{GL}_2(\mathbb A)$, and `finiteAdelicGL2Subgroup ℚ` is the kernel of the archimedean projection $\mathrm{GL}_2(\mathbb A)\to\mathrm{GL}_2(\mathbb A_\infty)$, i.e. the subgroup of matrices with trivial archimedean component. All adelic groups carry their Borel $\sigma$-algebras, $\mathrm{GL}_2(\mathbb R)$ carries the Borel structure as well, and `adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ` is the Haar measure on $\mathrm{GL}_2(\mathbb A)$ for that structure. For $g\in\mathrm{GL}_2(\mathbb A)$, `ratArchGL2 g` is the component of $g$ at the unique infinite place of $\mathbb Q$, transported to $\mathrm{GL}_2(\mathbb R)$, and `finFactor g` is the element $(\text{its image in }\mathrm{GL}_2(\mathbb A))^{-1}\cdot g$ of `finiteAdelicGL2Subgroup ℚ`, so that $g$ is the product of its archimedean and its finite part.
--
--   The data are: reals $c,u,d_1,d_2$; a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb A)$; a finite set $S$ of height-one primes of $\mathcal O_{\mathbb Q}$; functions $\varphi,\varphi':\mathrm{GL}_2(\mathbb A)\to\mathbb C$; functions $W_A,W_A',F_A:\mathrm{GL}_2(\mathbb R)\to\mathbb C$ and $W_f,W_f',F_f$ on `finiteAdelicGL2Subgroup ℚ`; a function $\Phi$ on $\mathbb A^2$; a function $P:\mathbb R\to\mathbb R$ and a real $x_0$; a set $D\subseteq\mathrm{GL}_2(\mathbb A)$; reals $e_1,e_2,c_S,u_S$ and a finite set $t_S$ of elements of $\mathrm{GL}_2(\mathbb A)$; a family $\varpi$ assigning to each prime $v$ an element of the $v$-adic integers $\mathcal O_v$; complex-valued families $\mathrm{lam},\mathrm{om},\mathrm{lam}',\mathrm{om}'$ on the primes; and a real $\kappa$.
--
--   Automorphy and decay of $\varphi,\varphi'$ (`_hφc`, `_hφ'c`, `_hφd`, `_hφ'd`, `_hφG`, `_hφ'G`): both are continuous, both satisfy `IsRapidlyDecreasingOnSiegelSets ℚ` — for all reals $c',u'$, all $t\in\mathrm{GL}_2(\mathbb A)$ with $0<c'$ and all $N\in\mathbb N$ there is a bound $C$ with $\|\varphi(g t)\|\,(1+\mathrm{archHeight}(g_\infty))^N\le C$ for all $g$ in the integral windowed Siegel set of parameters $c',u'$ — and both are invariant under left translation by the image of $\mathrm{GL}_2(\mathbb Q)$ under `globalPoints`.
--
--   The test vector $\Phi$ (`_hΦ`): $\Phi$ lies in `schwartzBruhat2 ℚ`, the $\mathbb C$-span of the pure tensors $x\mapsto g(x_\infty)h(x_{\mathrm{fin}})$ with $g$ Schwartz on $(\mathbb R^2)$-side mixed space and $h$ locally constant of compact support on $(\text{finite adeles})^2$.
--
--   The domain $D$ (`_he₁`, `_he`, `_hcS`, `_hDm`, `_hDμ`, `_hDs`, `_hDS`): $0<e_1<e_2$, $0<c_S$, $D$ is measurable of finite `adelicGLHaar`-measure, every $g\in D$ has $\mathrm{ideleNorm}(\det g)\in[e_1,e_2]$, and $D$ is contained in the union over $t\in t_S$ of the right translates by $t$ of the integral windowed Siegel set `integralWindowedSiegelSet ℚ cS uS`.
--
--   Factorisation of the Whittaker coefficients (`_hW`, `_hW'`): for every $g$, the Whittaker coefficient at $\alpha=1$ of $\varphi$ against the standard character `psiQ`, namely $\int \varphi(n(x)g)\,\psi(-x)\,d\nu(x)$ with $\nu$ the conditional measure of the adelic additive Haar measure on the box `adelicBox ℚ`, equals $W_A(\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{finFactor}\,g)$; likewise for $\varphi'$ against `psiQ⁻¹`, with $W_A',W_f'$. The measure is read off the `CarrierPins` record produced by `productionPinsOf` from the union over $x\in T$ of the right translates by $x$ of `centreCutSiegelSet ℚ c u d₁ d₂`, the level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap$ `finiteAdelicGL2Subgroup ℚ`, the Hecke generators `heckeGen`, and the box `adelicBox ℚ`; of these fields only the box enters the value of a Whittaker coefficient, the remaining parameters $c,u,d_1,d_2,T$ serving only as bookkeeping inside the record.
--
--   Factorisation and shape of $\Phi$ (`_hΦsplit`, `_hFA`): for every $g$, the value of $\Phi$ on the bottom row of $g$, $\Phi(\mathrm{bottomRowVec}\,g\,1)$, equals $F_A(\mathrm{ratArchGL2}\,g)\cdot F_f(\mathrm{finFactor}\,g)$, and $F_A$ is the Gaussian $F_A(g)=\exp\bigl(-\pi(g_{10}^2+g_{11}^2)\bigr)$ in the bottom row of $g\in\mathrm{GL}_2(\mathbb R)$.
--
--   The torus profile (`_hT`, `_hP0`, `_hPint`): for all reals $a_1\ne 0$ and $a_2>0$, the product $W_A\cdot W_A'$ evaluated at the diagonal matrix $\mathrm{diag}(a_1,a_2)$ (written `upperUnit a₁ 0 a₂`) equals the real number $P(a_1/a_2)$; $P\ge 0$ everywhere; and for every $\sigma'>x_0$ the function $y\mapsto P(y)\,|y|^{\sigma'-2}$ is integrable on $\mathbb R$.
--
--   Measurability and archimedean invariance (`_hWfm`, `_hWf'm`, `_hFfm`, `_harch`): $W_f,W_f',F_f$ are measurable; and `_harch` asserts the five clauses that $W_A$ and $W_A'$ are Borel measurable, $P$ is measurable, the product $W_A\cdot W_A'$ is invariant under left multiplication by elements of `realUnipotent` (the image of the unipotent homomorphism $\mathbb R\to\mathrm{GL}_2(\mathbb R)$), and $W_A\cdot W_A'$ is invariant under right multiplication by those $\kappa'$ in `rowIsometrySubgroup ℝ` (matrices of determinant of absolute value $1$ preserving the sum of squares of the two coordinates of a row vector acted on) with $\det\kappa'=1$.
--
--   Local data off $S$ (`hπ`, `_hfin`): the hypothesis `hπ` says that for $v\notin S$ the image of $\varpi_v$ in the completion $\mathbb Q_v$ is nonzero. The hypothesis `_hfin` has seven clauses: (i) for $v\notin S$, $\varpi_v$ has valuation $\exp(-1)$, i.e. is a uniformiser; (ii) for $v\notin S$, each of $\|\mathrm{lam}_v\|,\|\mathrm{om}_v\|,\|\mathrm{lam}'_v\|,\|\mathrm{om}'_v\|$ is at most $(\mathrm{absNorm}\,v)^{\kappa}$; (iii) the product $W_f\cdot(W_f'\cdot F_f)$ is invariant under left multiplication by elements of [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); (iv) for $v\notin S$ there is an additive character $\psi$ of $\mathbb Q_v$, trivial on $\mathcal O_v$ and nontrivial at some $r/\varpi_v$ with $r\in\mathcal O_v$, such that $W_f(\mathrm{finFactor}(\,\mathrm{placeEmbed}_v(\mathrm{unipotent}\,x)\cdot g))=\psi(x)\,W_f(\mathrm{finFactor}\,g)$ for all $x\in\mathbb Q_v$ and all $g$; (v) for $v\notin S$, $W_f\circ\mathrm{finFactor}$ is invariant under right multiplication by [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178); (vi) under the same right multiplications the product $W_f'\cdot F_f$ is invariant; (vii) the unramified recursion: for $v\notin S$, integers $m,n$ and $g$ with trivial $v$-component, the triple product $W_f\cdot W_f'\cdot F_f$ evaluated at $g\cdot\mathrm{placeEmbed}_v\bigl(\mathrm{diagZ}(\varpi_v,m)\cdot\mathrm{scalarPi}(\varpi_v)^n\bigr)$, i.e. at $g$ times the local diagonal matrix $\mathrm{diag}(\varpi_v^{m+n},\varpi_v^{n})$, equals the triple product at $g$ multiplied by $(\mathrm{om}_v\,\mathrm{om}'_v)^{n}\cdot \mathrm{heckeRecursionSeq}(N_v,\mathrm{lam}_v,\mathrm{om}_v)(m)\cdot\mathrm{heckeRecursionSeq}(N_v,\mathrm{lam}'_v,\mathrm{om}'_v)(m)$ when $0\le m$ and $0\le n$, and by $0$ otherwise; here $N_v=\mathrm{absNorm}\,v$ and `heckeRecursionSeq N lam om` is the sequence $1,\ \mathrm{lam}/N,\ (\mathrm{lam}\,x_{m+1}-\mathrm{om}\,x_m)/N$.
--
--   Boundedness and support at the bad places (`_hsupp`): there exist a compact set $\mathrm{Cpt}$ in `finiteAdelicGL2Subgroup ℚ` and a real $B_0$ such that $\|W_f(g)(W_f'(g)F_f(g))\|\le B_0$ for all $g$, and such that for every $g$ whose local component at each $v\notin S$ factors as $n'k'$ with $n'$ in the range of the local unipotent homomorphism and $k'$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), nonvanishing of $W_f(g)(W_f'(g)F_f(g))$ implies the existence of $n\in$ [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h\in\mathrm{Cpt}$ with $\mathrm{localAt}_v(n g)=\mathrm{localAt}_v(h)$ for every $v\in S$.
--
--   Conclusion. There exists a real $\sigma_d$ such that for every $s\in\mathbb C$ with $\sigma_d<\operatorname{Re} s$, and for every Haar measure $\nu_0$ on the idele group $\mathbb A^\times$, every Haar measure $\mu_f$ on `finiteAdelicGL2Subgroup ℚ`, every Haar measure $\mu_{N,\mathrm{arch}}$ on `realUnipotent` and every Haar measure $\mu_{N,\mathrm{fin}}$ on `finUnipotent`, the function
--   $$g\ \longmapsto\ \|\varphi(g)\varphi'(g)\|\cdot\Bigl(\|f_{s-1/2}(g)\|+\sum_{\xi\in\mathbb Q}\|f_{s-1/2}(w\,n(\xi)\,g)\|\Bigr)$$
--   is integrable on $D$ with respect to `adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ`. Here $f_{s-1/2}=\mathrm{godementSection}\ \mathbb Q\ \nu_0\ 1\ 1\ (\mathrm{moduleChar}\ \mathbb Q)$ at the parameter $s-1/2$ attached to $\Phi$, namely the product of the trivial characters at $\det g$, of $\mathrm{cpowChar}$ of the module character at exponent $s$, and of the Tate zeta integral of $t\mapsto\Phi(\mathrm{bottomRowVec}\,g\,t)$ against $\nu_0$ at exponent $2s$; $w=\mathrm{adelicWeyl}$ is the image in $\mathrm{GL}_2(\mathbb A)$ of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi)=\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ for $\xi\in\mathbb Q$ viewed in $\mathbb A$; and the sum over $\xi$ is the unconditional sum of the non-negative family of norms. The three measures $\mu_f$, $\mu_{N,\mathrm{arch}}$, $\mu_{N,\mathrm{fin}}$ are quantified over but do not occur in the integrand, which involves only $\nu_0$ and the Haar measure on $\mathrm{GL}_2(\mathbb A)$.
--
--   This is the integrability clause of the package of side conditions for the Rankin–Selberg integral over $\mathbb Q$: on the slab fundamental domain $D$, the folded integrand obtained from the cusp data $\varphi,\varphi'$ and the Godement section of $\Phi$ is absolutely integrable once $\operatorname{Re} s$ is large enough. It is cited by [`LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat), the statement assembling the analytic side conditions used to unfold the Rankin–Selberg integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrableOn_norm_mul_godementSection_majorant_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrableOn_norm_mul_godementSection_majorant_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (WA WA' FA : GL (Fin 2) ℝ → ℂ) (Wf Wf' Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
    (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (P : ℝ → ℝ) (x₀ : ℝ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (e₁ e₂ cS uS : ℝ) (tS : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hφc : Continuous φ) (_hφ'c : Continuous φ')
    (_hφd : IsRapidlyDecreasingOnSiegelSets ℚ φ) (_hφ'd : IsRapidlyDecreasingOnSiegelSets ℚ φ')
    (_hφG : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (_hφ'G : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (globalPoints (𝓞 ℚ) ℚ γ * g) = φ' g)
    (_hΦ : Φ ∈ schwartzBruhat2 ℚ)
    (_he₁ : 0 < e₁) (_he : e₁ < e₂) (_hcS : 0 < cS) (_hDm : MeasurableSet D)
    (_hDμ : adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ D < ⊤)
    (_hDs : D ⊆ {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (_hDS : D ⊆ ⋃ t ∈ tS, (· * t) '' integralWindowedSiegelSet ℚ cS uS)
    (_hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g))
    (_hW' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g = WA' (ratArchGL2 g) * Wf' (finFactor g))
    (_hΦsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Φ (bottomRowVec ℚ g 1) = FA (ratArchGL2 g) * Ff (finFactor g))
    (_hFA : ∀ g : GL (Fin 2) ℝ, FA g = Complex.exp (-(Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))
    (_hT : ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
      WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') * WA' (upperUnit a₁ 0 a₂ h₁ h₂.ne') = ((P (a₁ / a₂) : ℝ) : ℂ))
    (_hP0 : ∀ y : ℝ, 0 ≤ P y)
    (_hPint : ∀ σ' : ℝ, x₀ < σ' → Integrable (fun y : ℝ => P y * |y| ^ (σ' - 2)))
    (_hWfm : Measurable Wf) (_hWf'm : Measurable Wf') (_hFfm : Measurable Ff)
    (_harch : @Measurable (GL (Fin 2) ℝ) ℂ (borel _) _ WA ∧ @Measurable (GL (Fin 2) ℝ) ℂ (borel _) _ WA' ∧ Measurable P ∧
      (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, WA (n * g) * WA' (n * g) = WA g * WA' g) ∧
      (∀ κ' ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ' = 1 →
        ∀ g : GL (Fin 2) ℝ, WA (g * κ') * WA' (g * κ') = WA g * WA' g))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (_hfin :
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        Wf ((n : finiteAdelicGL2Subgroup ℚ) * g) * (Wf' ((n : finiteAdelicGL2Subgroup ℚ) * g) * Ff ((n : finiteAdelicGL2Subgroup ℚ) * g)) =
          Wf g * (Wf' g * Ff g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ →
          Wf' (finFactor (g * placeEmbed ℚ v x)) * Ff (finFactor (g * placeEmbed ℚ v x)) = Wf' (finFactor g) * Ff (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ hv : v ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
        Wf (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
          (Wf' (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
            Ff (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)))) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om v * om' v) ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) m.toNat
         else 0) * (Wf (finFactor g) * (Wf' (finFactor g) * Ff (finFactor g)))))
    (_hsupp :
      (∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
        (∀ g : finiteAdelicGL2Subgroup ℚ, ‖Wf g * (Wf' g * Ff g)‖ ≤ B₀) ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf g * (Wf' g * Ff g) ≠ 0 →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)))
    :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∃ σd : ℝ, ∀ s : ℂ, σd < s.re →
      ∀ (ν₀ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [ν₀.IsHaarMeasure]
        (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
        (μNArch : Measure realUnipotent) [μNArch.IsHaarMeasure]
        (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
      IntegrableOn (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ‖φ g * φ' g‖ *
          (‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) g‖ +
            ∑' ξ : ℚ, ‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2)
              (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ) * g)‖))
        D (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by sorry
