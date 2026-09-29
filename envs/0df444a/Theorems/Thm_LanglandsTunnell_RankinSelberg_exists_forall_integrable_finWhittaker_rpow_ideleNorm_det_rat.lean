-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/c46789e5-24a5-5a63-9de3-0ee5120da18f
-- title:
--   Integrability of the finite Rankin–Selberg integrand over ℚ
-- statement:
--   The ambient field is $\mathbb{Q}$, with $\mathbb{A} =$ `AdeleRing (𝓞 ℚ) ℚ`, the adelic group $G(\mathbb{A}) =$ `AdelicGL2 (𝓞 ℚ) ℚ` $= \mathrm{GL}_2(\mathbb{A})$ carrying its Borel structure and Haar measure `adelicGLHaar`, and `finiteAdelicGL2Subgroup ℚ` the kernel of the archimedean projection `glArch`, i.e. the subgroup of adelic matrices whose archimedean component is trivial.
--
--   The data are: real parameters $c, u, d_1, d_2$; a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A})$; a finite set $S$ of height-one primes of $\mathbb{Z}$; two functions $\varphi, \varphi' : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$; archimedean factors $W_A, W_A', F_A : \mathrm{GL}_2(\mathbb{R}) \to \mathbb{C}$ and finite factors $W_f, W_f', F_f$ on `finiteAdelicGL2Subgroup ℚ`; a function $\Phi$ on $\mathbb{A}^2$; a function $P : \mathbb{R} \to \mathbb{R}$ and an abscissa $x_0 \in \mathbb{R}$; a subset $D \subseteq \mathrm{GL}_2(\mathbb{A})$, reals $e_1, e_2, c_S, u_S$ and a finite set $t_S$ of elements of $\mathrm{GL}_2(\mathbb{A})$.
--
--   The hypotheses on the automorphic side are: `_hφc`, `_hφ'c` (continuity of $\varphi$ and $\varphi'$); `_hφd`, `_hφ'd`, asserting `IsRapidlyDecreasingOnSiegelSets ℚ` for both, that is, for all reals $c, u$, all $t \in \mathrm{GL}_2(\mathbb{A})$ with $c > 0$ and all $N \in \mathbb{N}$ there is a bound $C$ with $\|\varphi(gt)\|\,(1 + \mathrm{archHeight}(g))^N \le C$ for all $g$ in `integralWindowedSiegelSet ℚ c u` (the set of $g$ whose finite part lies in `finiteIntegralGL2`, with $c \le \mathrm{archHeight}$ and window bound $\mathrm{xWindowSq} \le u^2$ at each infinite place); `_hφG`, `_hφ'G`, left invariance of $\varphi$, $\varphi'$ under the image of $\mathrm{GL}_2(\mathbb{Q})$ under `globalPoints`; and `_hΦ`, that $\Phi$ lies in `schwartzBruhat2 ℚ`, the $\mathbb{C}$-span of the pure tensors $\Phi(x) = g(x_\infty)\,h(x_{\mathrm{fin}})$ with $g$ Schwartz on the mixed space and $h$ locally constant of compact support.
--
--   The hypotheses on the truncation domain $D$ are: `_he₁`, `_he`, `_hcS` ($0 < e_1 < e_2$ and $0 < c_S$); `_hDm`, `_hDμ` ($D$ measurable of finite `adelicGLHaar` measure); `_hDs`, that $D$ lies in the slab where the idele norm of $\det g$ (Tate's `ideleNorm`, the value of the distributive Haar character of $\mathbb{A}$) lies in $[e_1, e_2]$; and `_hDS`, that $D$ is covered by the right translates of `integralWindowedSiegelSet ℚ cS uS` by the elements of $t_S$.
--
--   The hypotheses tying the test data to their pure-tensor factorisations are: `_hW` and `_hW'`, which state that for every $g$ the Whittaker coefficient `whittakerCoefficient` at $\alpha = 1$ — the integral $\int \varphi(u(x) g)\,\psi(-x)\,d\nu$ over $\mathbb{A}$ against the carrier data `productionPinsOf ℚ` built from the union of the right translates by $x \in T$ of `centreCutSiegelSet ℚ c u d₁ d₂`, the level subgroups $N \mapsto$ `levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ`, the Hecke generators `heckeGen`, and the conditional additive Haar measure on `adelicBox ℚ` — equals $W_A(\mathrm{ratArchGL2}\,g)\,W_f(\mathrm{finFactor}\,g)$ for the standard character `psiQ` and $\varphi$, and $W_A'(\mathrm{ratArchGL2}\,g)\,W_f'(\mathrm{finFactor}\,g)$ for `psiQ`$^{-1}$ and $\varphi'$; `_hΦsplit`, that $\Phi$ evaluated on the bottom row vector `bottomRowVec ℚ g 1` equals $F_A(\mathrm{ratArchGL2}\,g)\,F_f(\mathrm{finFactor}\,g)$; and `_hFA`, that $F_A(g) = \exp(-\pi(g_{10}^2 + g_{11}^2))$ is the Gaussian in the bottom row.
--
--   The hypotheses on the torus profile and measurability are: `_hT`, that for $a_1 \ne 0$ and $a_2 > 0$ the product $W_A W_A'$ at the upper-triangular matrix `upperUnit a₁ 0 a₂` equals $P(a_1/a_2)$; `_hP0`, that $P \ge 0$; `_hPint`, that $y \mapsto P(y)|y|^{\sigma' - 2}$ is integrable for every $\sigma' > x_0$; `_hWfm`, `_hWf'm`, `_hFfm`, measurability of $W_f$, $W_f'$, $F_f$; and `_harch` (five clauses), requiring Borel measurability of $W_A$, $W_A'$ and measurability of $P$, together with the invariance of the product $W_A W_A'$ under left multiplication by elements of `realUnipotent` (the image of the unipotent homomorphism over $\mathbb{R}$) and under right multiplication by elements of `rowIsometrySubgroup ℝ` of determinant $1$.
--
--   The finite-place data are a family $\varpi$ of elements of the valuation rings $\mathcal{O}_v$, the hypothesis `hπ` that $\varpi_v \ne 0$ in $\mathbb{Q}_v$ for $v \notin S$, four complex-valued tables $\mathrm{lam}, \mathrm{om}, \mathrm{lam}', \mathrm{om}'$ on the places, and an exponent $\kappa \in \mathbb{R}$. The hypothesis `_hfin` (seven clauses, summarised here) requires, for $v \notin S$: that $\varpi_v$ is a uniformiser, $v(\varpi_v) = \exp(-1)$; that the four tables are bounded by $N(v)^{\kappa}$ in absolute value; that the product $g \mapsto W_f(g)\,(W_f'(g)\,F_f(g))$ is invariant under left translation by [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); that there is an additive character $\psi$ of $\mathbb{Q}_v$ trivial on $\mathcal{O}_v$ and nontrivial on $\varpi_v^{-1}\mathcal{O}_v$ with $W_f(\mathrm{finFactor}(\mathrm{placeEmbed}(u(x))\,g)) = \psi(x)\,W_f(\mathrm{finFactor}\,g)$; that $W_f$, and likewise the product $W_f' F_f$, is invariant under right translation by [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178); and the unramified torus law: for $v \notin S$, $g$ with trivial component at $v$, and integers $m, n$, the value of $W_f\,(W_f'\,F_f)$ at $g$ right-translated by $\mathrm{diagZ}(\varpi_v, m)\,\mathrm{scalarPi}(\varpi_v)^n$ equals $\big[(\mathrm{om}_v\,\mathrm{om}'_v)^{n}\,\mathrm{heckeRecursionSeq}(N(v), \mathrm{lam}_v, \mathrm{om}_v)(m)\,\mathrm{heckeRecursionSeq}(N(v), \mathrm{lam}'_v, \mathrm{om}'_v)(m)\big]$ when $0 \le m$ and $0 \le n$ (and $0$ otherwise) times the value of $W_f\,(W_f'\,F_f)$ at $g$.
--
--   The hypothesis `_hsupp` requires a compact set $\mathrm{Cpt}$ in `finiteAdelicGL2Subgroup ℚ` and a real $B_0$ such that $\|W_f(g)(W_f'(g)F_f(g))\| \le B_0$ for all $g$, and such that every $g$ whose local component at each $v \notin S$ factors as a unipotent element times an element of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) and at which $W_f(g)(W_f'(g)F_f(g)) \ne 0$ admits $n \in$ [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h \in \mathrm{Cpt}$ with $n g$ and $h$ having the same local component at every $v \in S$.
--
--   Conclusion. With $\mathrm{GL}_2(\mathbb{R})$ given its Borel structure, there exists a real abscissa $\sigma_D$ such that for every $s \in \mathbb{C}$ with $\sigma_D < \operatorname{Re} s$, and for all Haar measures $\nu_0$ on the idele group $\mathbb{A}^{\times}$, $\mu_f$ on `finiteAdelicGL2Subgroup ℚ`, $\mu_{N,\infty}$ on `realUnipotent` and $\mu_{N,\mathrm{fin}}$ on `finUnipotent`, the function
--   $$g \longmapsto W_f(\mathrm{finFactor}\,g)\,\big(W_f'(\mathrm{finFactor}\,g)\,F_f(\mathrm{finFactor}\,g)\big)\cdot \big\| \det g \big\|_{\mathbb{A}}^{\,s + 1/2 - 1/2}$$
--   on `finiteAdelicGL2Subgroup ℚ` is integrable with respect to $\mu_f$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to the subgroup `finUnipotent` and the measure $\mu_{N,\mathrm{fin}}$; here $\|\det g\|_{\mathbb{A}}$ is Tate's `ideleNorm` of the determinant of $g$ viewed in $\mathrm{GL}_2(\mathbb{A})$, coerced to $\mathbb{C}$, and the complex exponent is written $s + 1/2 - 1/2$. The measures $\nu_0$ and $\mu_{N,\infty}$ are quantified over but do not occur in the asserted integrability.
--
--   This is the finite-place integrability condition in the list of side conditions for the $\mathrm{GL}_2 \times \mathrm{GL}_2$ Rankin–Selberg integral over $\mathbb{Q}$: for $\operatorname{Re} s$ large the finite Whittaker–Schwartz integrand $W_f (W_f' F_f)\|\det\|^s$ is integrable on the unipotent quotient of $\mathrm{GL}_2$ of the finite adeles. It is used by the statements assembling the Rankin–Selberg side conditions over $\mathbb{Q}$ and the factorisation of the global integral into archimedean and finite parts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat
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
      Integrable
        (fun g : finiteAdelicGL2Subgroup ℚ => (Wf (finFactor g) * (Wf' (finFactor g) * Ff (finFactor g))) *
          ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by sorry
