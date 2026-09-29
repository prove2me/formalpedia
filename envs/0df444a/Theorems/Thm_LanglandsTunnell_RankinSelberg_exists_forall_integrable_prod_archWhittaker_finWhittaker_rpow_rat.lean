-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_prod_archWhittaker_finWhittaker_rpow_rat
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_prod_archWhittaker_finWhittaker_rpow_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/dd1c7c58-0961-5c72-9ce0-b58bd415f4ba
-- title:
--   Integrability of the split Rankin–Selberg integrand over ℚ
-- statement:
--   The data are: real parameters $c,u,d_1,d_2$; a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ and a finite set $S$ of finite places of $\mathbb{Q}$; two functions $\varphi,\varphi' : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$; archimedean factors $W_A, W_A', F_A : \mathrm{GL}_2(\mathbb{R}) \to \mathbb{C}$ and finite factors $W_f, W_f', F_f$ on `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean projection `glArch` on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$; a function $\Phi$ on $\mathbb{A}_{\mathbb{Q}}^2$; a function $P : \mathbb{R} \to \mathbb{R}$ and an abscissa $x_0 \in \mathbb{R}$; a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ together with reals $e_1, e_2, c_S, u_S$ and a finite set $t_S$ of adelic points; a choice $\varpi$ of an element of the ring of integers of each completion; functions $\mathrm{lam}, \mathrm{om}, \mathrm{lam}', \mathrm{om}'$ from finite places to $\mathbb{C}$; and a real $\kappa$.
--
--   The hypotheses fall into the following groups.
--
--   *Automorphy and decay of $\varphi, \varphi'$.* Both are continuous; both satisfy `IsRapidlyDecreasingOnSiegelSets ℚ`, i.e. for all reals $c', u'$, all adelic $t$ with $0 < c'$ and all $N \in \mathbb{N}$ there is a constant bounding $\|\varphi(g t)\| (1 + \mathrm{archHeight}(g_\infty))^N$ for $g$ in the integral windowed Siegel set of parameters $c', u'$; and both are left invariant under the image of $\mathrm{GL}_2(\mathbb{Q})$ under `globalPoints`.
--
--   *The Schwartz–Bruhat datum.* $\Phi$ lies in `schwartzBruhat2 ℚ`, the $\mathbb{C}$-span of the pure tensors $x \mapsto g((x_i)_\infty) h((x_i)_{\mathrm{fin}})$ with $g$ Schwartz on the mixed space and $h$ locally constant with compact support on $(\mathbb{A}_{\mathbb{Q},\mathrm{fin}})^2$.
--
--   *The slab domain.* $0 < e_1 < e_2$, $0 < c_S$, the set $D$ is measurable of finite adelic Haar measure, is contained in the locus where the idele norm of $\det g$ lies in $[e_1, e_2]$, and is covered by the right translates by the elements of $t_S$ of the integral windowed Siegel set of parameters $c_S, u_S$.
--
--   *Whittaker splitting.* For every $g$, the Whittaker coefficient at $\alpha = 1$ of $\varphi$ against the standard character `psiQ`, taken with respect to the carrier pins `productionPinsOf ℚ` whose domain is the union over $x \in T$ of the right translates by $x$ of the centre-cut Siegel set `centreCutSiegelSet ℚ c u d₁ d₂` (the adelic points with integral finite part, with local height at least $c$, window $\mathrm{xWindowSq} \le u^2$ and archimedean determinant norm in $[d_1,d_2]$ at each infinite place), whose level subgroups are `levelOne ⊓ finiteAdelicGL2Subgroup ℚ`, whose Hecke generators are `heckeGen`, and whose additive measure is the adelic additive Haar measure conditioned on the adelic box — that is, $\int_{\mathbb{A}} \varphi(u(x) g)\, \mathrm{psiQ}(-x)\,d\nu(x)$ for that conditional measure $\nu$ — equals $W_A(\mathrm{ratArchGL2}\,g) \cdot W_f(\mathrm{finFactor}\,g)$, where `ratArchGL2` is the real $\mathrm{GL}_2$-component at the infinite place of $\mathbb{Q}$ and `finFactor` removes it. Correspondingly, the coefficient of $\varphi'$ against $\mathrm{psiQ}^{-1}$ equals $W_A'(\mathrm{ratArchGL2}\,g) \cdot W_f'(\mathrm{finFactor}\,g)$.
--
--   *Splitting and shape of $\Phi$.* For every $g$, the value of $\Phi$ on the bottom row vector $\mathrm{bottomRowVec}\,g\,1$ equals $F_A(\mathrm{ratArchGL2}\,g) \cdot F_f(\mathrm{finFactor}\,g)$, and $F_A(g) = \exp(-\pi(g_{10}^2 + g_{11}^2))$ for all $g \in \mathrm{GL}_2(\mathbb{R})$.
--
--   *The torus profile.* For $a_1 \ne 0$ and $a_2 > 0$, $W_A \cdot W_A'$ evaluated at the upper triangular matrix $\mathrm{upperUnit}(a_1, 0, a_2)$ equals $P(a_1/a_2)$; $P \ge 0$ everywhere; and for every $\sigma' > x_0$ the function $y \mapsto P(y)|y|^{\sigma'-2}$ is integrable on $\mathbb{R}$.
--
--   *Measurability and archimedean invariance.* $W_f, W_f', F_f$ are measurable; the hypothesis `_harch` asserts that $W_A$ and $W_A'$ are Borel measurable, that $P$ is measurable, that $W_A \cdot W_A'$ is invariant under left multiplication by elements of `realUnipotent` (the image of the upper unipotent homomorphism over $\mathbb{R}$), and that it is invariant under right multiplication by elements of `rowIsometrySubgroup ℝ` of determinant $1$.
--
--   *Uniformiser data.* For $v \notin S$ the image of $\varpi_v$ in the completion is nonzero (hypothesis `hπ`).
--
--   *Finite-place behaviour.* The hypothesis `_hfin` is a conjunction of seven clauses: off $S$ the element $\varpi_v$ has valuation $\exp(-1)$, so is a uniformiser; off $S$ the four Satake-type parameters satisfy $\|\mathrm{lam}_v\|, \|\mathrm{om}_v\|, \|\mathrm{lam}'_v\|, \|\mathrm{om}'_v\| \le (\#\mathcal{O}/v)^{\kappa}$; the product $W_f \cdot (W_f' \cdot F_f)$ is invariant under left multiplication by [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); off $S$ there is an additive character $\psi$ of the completion at $v$ which is trivial on the local integers, nontrivial on some $r/\varpi_v$, and with respect to which $W_f$ satisfies $W_f(\mathrm{finFactor}(n(x) g)) = \psi(x) W_f(\mathrm{finFactor}\,g)$ for the local unipotent $n(x)$ embedded at $v$; off $S$, $W_f \circ \mathrm{finFactor}$ is invariant under right multiplication by elements of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) embedded at $v$, and likewise the product $W_f' \cdot F_f$; and finally the unramified torus law: off $S$, for $g$ whose $v$-component is trivial and for integers $m, n$, the value of $W_f \cdot (W_f' \cdot F_f)$ at $g$ multiplied at $v$ by $\mathrm{diag}(\varpi_v^m, 1)\,(\varpi_v I)^n$ equals the value at $g$ times the factor $(\mathrm{om}_v \mathrm{om}'_v)^{n} \cdot \mathrm{heckeRecursionSeq}(N_v, \mathrm{lam}_v, \mathrm{om}_v)(m) \cdot \mathrm{heckeRecursionSeq}(N_v, \mathrm{lam}'_v, \mathrm{om}'_v)(m)$ if $0 \le m$ and $0 \le n$, and zero otherwise, where $N_v$ is the absolute norm of $v$ and `heckeRecursionSeq` is the sequence $a_0 = 1$, $a_1 = \mathrm{lam}/N$, $a_{m+2} = (\mathrm{lam}\,a_{m+1} - \mathrm{om}\,a_m)/N$.
--
--   *Support control.* The hypothesis `_hsupp` provides a compact set $\mathrm{Cpt}$ in the finite-adelic subgroup and a bound $B_0$ such that $\|W_f(g)(W_f'(g) F_f(g))\| \le B_0$ for all $g$, and such that whenever $g$ has, at every $v \notin S$, a local component of the form $n' k'$ with $n'$ in the image of the local unipotent homomorphism and $k'$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), and whenever $W_f(g)(W_f'(g) F_f(g)) \ne 0$, there exist $n \in$ [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h \in \mathrm{Cpt}$ with $n g$ and $h$ having the same local components at all $v \in S$.
--
--   Conclusion (with $\mathrm{GL}_2(\mathbb{R})$ carrying its Borel $\sigma$-algebra): there exists $\sigma_d \in \mathbb{R}$ such that for every $s \in \mathbb{C}$ with $\sigma_d < \operatorname{Re} s$, and for every Haar measure $\nu_0$ on the idele group $(\mathbb{A}_{\mathbb{Q}})^\times$, every Haar measure $\mu_f$ on `finiteAdelicGL2Subgroup ℚ`, every Haar measure $\mu_{N,\infty}$ on `realUnipotent` and every Haar measure $\mu_{N,\mathrm{fin}}$ on `finUnipotent`, the function
--   $$(g_\infty, g_{\mathrm{fin}}) \mapsto \bigl(W_A(g_\infty)\,(W_A'(g_\infty) F_A(g_\infty))\cdot |\det g_\infty|^{(s - 1/2 + 1) - 1/2}\bigr)\cdot\bigl(W_f(g_{\mathrm{fin}})\,(W_f'(g_{\mathrm{fin}}) F_f(g_{\mathrm{fin}}))\cdot \|\det g_{\mathrm{fin}}\|^{(s - 1/2 + 1) - 1/2}\bigr)$$
--   on $\mathrm{GL}_2(\mathbb{R}) \times$ `finiteAdelicGL2Subgroup ℚ` is integrable for the product of the measure `archMeasure` (Lebesgue measure on $2 \times 2$ real matrices pulled back to $\mathrm{GL}_2(\mathbb{R})$ with density $|\det|^{-2}$) weighted by the density [`HaarQuotient.density realUnipotent μNArch`](def/HaarQuotient.html#L25), and of $\mu_f$ weighted by the density [`HaarQuotient.density finUnipotent μNFin`](def/HaarQuotient.html#L25). Here the archimedean power is the complex power of the real absolute value of $\det g_\infty$, and the finite power is the complex power of `TateGlobal.ideleNorm` of $\det g_{\mathrm{fin}}$ regarded adelically. The Haar measure $\nu_0$ on the idele group is quantified over without occurring in the integrand or in the measure.
--
--   This is the integrability side condition for the split form of the Rankin–Selberg integral over $\mathbb{Q}$: after the Whittaker functions and the Schwartz–Bruhat section have been written as products of an archimedean and a finite factor, the resulting integrand on $\mathrm{GL}_2(\mathbb{R}) \times \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q},\mathrm{fin}})$ is integrable in a right half plane for the product of the two density-weighted quotient measures. It is one conjunct of the collected Rankin–Selberg side conditions over $\mathbb{Q}$, [`LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat), and is obtained here by combining the separate archimedean and finite integrability statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_prod_archWhittaker_finWhittaker_rpow_rat.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_prod_archWhittaker_finWhittaker_rpow_rat
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
      Integrable (fun p : GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ =>
          ((WA p.1 * (WA' p.1 * FA p.1)) *
              (((|(Matrix.GeneralLinearGroup.det p.1 : ℝ)| : ℝ) : ℂ) ^ ((s - 1 / 2 + 1) - 1 / 2))) *
            ((Wf p.2 * (Wf' p.2 * Ff p.2)) *
              ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ)
                ^ ((s - 1 / 2 + 1) - 1 / 2))))
        ((archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)).prod
          (μf.withDensity (HaarQuotient.density finUnipotent μNFin))) := by sorry
