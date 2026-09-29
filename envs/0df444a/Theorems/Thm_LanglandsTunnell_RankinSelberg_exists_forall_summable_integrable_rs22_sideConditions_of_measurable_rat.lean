-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/c965ae6a-872f-56b2-8c86-d5a27ecba29e
-- title:
--   Rankin–Selberg side conditions for GL₂timesGL₂ over ℚ
-- statement:
--   Throughout, $\mathrm{GL}_2(\mathbb{A})$ denotes `AdelicGL2 (𝓞 ℚ) ℚ`, the general linear group of rank $2$ over the adele ring of $\mathbb{Q}$; `finiteAdelicGL2Subgroup ℚ` is the kernel of the archimedean projection `glArch`, `ratArchGL2 g` is the real $\mathrm{GL}_2$-component of $g$ at the unique infinite place of $\mathbb{Q}$, and `finFactor g` is $g$ with that archimedean component divided out. Whittaker coefficients are taken with respect to the carrier record $\mathtt{pins} =$ `productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)`; by the definition of `whittakerCoefficient`, only the additive datum of the record enters, so that for a character $\psi$ of $\mathbb{A}$ and $\alpha = 1$ the coefficient at $g$ is $\int \varphi(n(x)g)\,\psi(-x)\,d\nu(x)$, where $n(x)$ is the upper unipotent matrix with entry $x$ and $\nu$ is the adelic additive Haar measure conditioned on the box `adelicBox ℚ`. The characters used are [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615) and its inverse.
--
--   The data are: real parameters $c, u, d_1, d_2$; a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A})$ and a finite set $S$ of finite places of $\mathbb{Q}$; functions $\varphi, \varphi' : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$; functions $W_A, W_A', F_A$ on $\mathrm{GL}_2(\mathbb{R})$ and $W_f, W_f', F_f$ on `finiteAdelicGL2Subgroup ℚ`; a function $\Phi$ on $\mathbb{A}^2$; a real function $P$ and a real abscissa $x_0$; a set $D \subseteq \mathrm{GL}_2(\mathbb{A})$; reals $e_1, e_2, c_S, u_S$ and a finite set $t_S$ of elements of $\mathrm{GL}_2(\mathbb{A})$.
--
--   The hypotheses fall into the following groups. (i) Analytic hypotheses on the test vectors: $\varphi$ and $\varphi'$ are continuous, each satisfies `IsRapidlyDecreasingOnSiegelSets ℚ` (for all $c,u$, all $t$ with $c>0$ and every $N$ there is a bound $C$ with $\|\varphi(gt)\|\,(1+\mathrm{archHeight}(g))^N \le C$ for $g$ in the integral windowed Siegel set `integralWindowedSiegelSet ℚ c u`), and each is invariant under left translation by the global points `globalPoints (𝓞 ℚ) ℚ γ`, $\gamma \in \mathrm{GL}_2(\mathbb{Q})$; moreover $\Phi$ lies in `schwartzBruhat2 ℚ`, the $\mathbb{C}$-span of pure tensors of a Schwartz function on the mixed space with a locally constant compactly supported function on $(\mathbb{A}_{\mathrm{fin}})^2$. (ii) Hypotheses on the domain $D$: $0 < e_1 < e_2$, $0 < c_S$, $D$ is measurable with finite `adelicGLHaar` measure, $D$ is contained in the slab where the idelic norm of $\det$ lies in $[e_1,e_2]$, and $D$ is contained in the union of the right translates $(\cdot * t)\,[\,$`integralWindowedSiegelSet ℚ cS uS`$\,]$ over $t \in t_S$. (iii) Factorisation hypotheses: the Whittaker coefficient of $\varphi$ against $\psi_{\mathbb{Q}}$ at $\alpha = 1$ equals $W_A(\mathrm{ratArchGL2}\,g)\,W_f(\mathrm{finFactor}\,g)$, that of $\varphi'$ against $\psi_{\mathbb{Q}}^{-1}$ equals $W_A'(\mathrm{ratArchGL2}\,g)\,W_f'(\mathrm{finFactor}\,g)$, and $\Phi(\mathrm{bottomRowVec}\,g\,1) = F_A(\mathrm{ratArchGL2}\,g)\,F_f(\mathrm{finFactor}\,g)$, with $F_A(g) = \exp(-\pi(g_{10}^2 + g_{11}^2))$. (iv) Torus-profile hypotheses: for $a_1 \neq 0$ and $a_2 > 0$ one has $W_A(\mathrm{upperUnit}\,a_1\,0\,a_2)\,W_A'(\mathrm{upperUnit}\,a_1\,0\,a_2) = P(a_1/a_2)$, $P \ge 0$, and $y \mapsto P(y)|y|^{\sigma'-2}$ is integrable for every $\sigma' > x_0$. (v) Measurability and archimedean invariance: $W_f, W_f', F_f$ are measurable, and the clause `_harch` requires $W_A$, $W_A'$ measurable for the Borel structure on $\mathrm{GL}_2(\mathbb{R})$, $P$ measurable, the product $W_AW_A'$ invariant under left translation by the unipotent subgroup `realUnipotent` and under right translation by determinant-one elements of `rowIsometrySubgroup ℝ`.
--
--   (vi) Local data off $S$: a family $\varpi_v$ of elements of the valuation rings $\mathcal{O}_v$, with $\varpi_v \neq 0$ in $\mathbb{Q}_v$ for $v \notin S$ (hypothesis `hπ`), complex tables $\lambda, \omega, \lambda', \omega'$ indexed by the finite places, and a real exponent $\kappa$. The hypothesis `_hfin` (seven clauses, summarised here) requires: $\varpi_v$ is a uniformiser at each $v \notin S$ (valuation $\mathrm{exp}(-1)$); the four tables satisfy $\|\lambda(v)\|, \|\omega(v)\|, \|\lambda'(v)\|, \|\omega'(v)\| \le \mathrm{N}(v)^{\kappa}$ for $v \notin S$; the product $W_f\,(W_f'F_f)$ is invariant under left translation by [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); for each $v \notin S$ there is an additive character $\psi$ of $\mathbb{Q}_v$, trivial on $\mathcal{O}_v$ and non-trivial on $\varpi_v^{-1}\mathcal{O}_v$, through which $W_f$ transforms under left translation by local unipotents at $v$; $W_f$ is right invariant under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) at each $v \notin S$, and so is the product $W_f'F_f$; and finally, for $v \notin S$, $g$ with trivial component at $v$, and integers $m,n$, translating $g$ on the right by the image under `placeEmbed` of $\mathrm{diagZ}(\varpi_v)^{\,}$ at exponent $m$ times $\mathrm{scalarPi}(\varpi_v)^n$ multiplies $W_f\,(W_f'F_f)$ by $(\omega(v)\omega'(v))^{n}\,\mathrm{heckeRecursionSeq}(\mathrm{N}(v),\lambda(v),\omega(v))_m\,\mathrm{heckeRecursionSeq}(\mathrm{N}(v),\lambda'(v),\omega'(v))_m$ when $m,n \ge 0$ and by $0$ otherwise. (vii) The support hypothesis `_hsupp`: there are a compact set $\mathrm{Cpt}$ in `finiteAdelicGL2Subgroup ℚ` and a bound $B_0$ such that $\|W_f(g)(W_f'(g)F_f(g))\| \le B_0$ for all $g$, and such that whenever $g$ factors locally at every $v \notin S$ as a unipotent times an element of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) and $W_f(g)(W_f'(g)F_f(g)) \neq 0$, there exist $n$ in [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h \in \mathrm{Cpt}$ with $ng$ and $h$ having the same component at every $v \in S$.
--
--   The conclusion, stated with $\mathrm{GL}_2(\mathbb{R})$ carrying its Borel $\sigma$-algebra, is the conjunction of the following.
--
--   First, left unipotent invariance: for every $n$ in `adelicUnipotent ℚ` (the range of `unipotentGL2Hom` over $\mathbb{A}$) and every $g$, the product of the Whittaker coefficient of $\varphi$ against $\psi_{\mathbb{Q}}$ and that of $\varphi'$ against $\psi_{\mathbb{Q}}^{-1}$, both at $\alpha = 1$, takes the same value at $ng$ as at $g$.
--
--   Secondly, there exists a real abscissa $\sigma_d$ such that for every $s \in \mathbb{C}$ with $\sigma_d < \mathrm{Re}\,s$, and for every choice of Haar measures $\nu_0$ on the idele group, $\mu_f$ on `finiteAdelicGL2Subgroup ℚ`, $\mu_{N,\mathrm{arch}}$ on `realUnipotent` and $\mu_{N,\mathrm{fin}}$ on `finUnipotent`, the following six assertions hold. (a) The function $g \mapsto$ (Whittaker coefficient of $\varphi$) $\cdot$ (Whittaker coefficient of $\varphi'$) $\cdot\;$`rs22Kernel ℚ 1 (moduleChar ℚ) _ Φ (s - 1/2) g` is measurable; here the kernel is the value of the trivial character at $\det g$ times `cpowChar` of the module character `moduleChar ℚ` at exponent $(s-1/2)+1/2$ evaluated at $\det g$, times $\Phi(\mathrm{bottomRowVec}\,g\,1)$. (b) For every $g \in D$ the family $\xi \mapsto \|\,$`godementSection ℚ ν₀ 1 1 (moduleChar ℚ) _ Φ (s - 1/2)` $(w\,n(\xi)\,g)\|$, indexed by $\xi \in \mathbb{Q}$, is summable, where $w =$ `adelicWeyl (𝓞 ℚ) ℚ` and $n(\xi) =$ `unipotentGL2` of the image of $\xi$ in $\mathbb{A}$. (c) The function $g \mapsto \|\varphi(g)\varphi'(g)\|\,\bigl(\|\mathrm{godementSection}(g)\| + \sum_{\xi \in \mathbb{Q}} \|\mathrm{godementSection}(w\,n(\xi)\,g)\|\bigr)$, with the same Godement section at $s - 1/2$, is integrable on $D$ for `adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ`. (d) The function $q \mapsto \|\,$(Whittaker coefficient of $\varphi$ at $q.\mathrm{out}$)$\,\cdot\,$(Whittaker coefficient of $\varphi'$ at $q.\mathrm{out}$)$\,\cdot\,$`rs22Kernel ℚ 1 (moduleChar ℚ) _ Φ (s - 1/2)` $q.\mathrm{out}\|$, where $q.\mathrm{out}$ is a chosen representative of the class $q$ in `UnipotentQuotient ℚ`, is integrable for `unipotentQuotientMeasure ℚ`. (e) The function $(p_1,p_2) \mapsto \bigl(W_A(p_1)(W_A'(p_1)F_A(p_1))\bigr)\,|\det p_1|^{(s-1/2+1)-1/2}\cdot\bigl(W_f(p_2)(W_f'(p_2)F_f(p_2))\bigr)\,\bigl(\mathrm{ideleNorm}(\det p_2)\bigr)^{(s-1/2+1)-1/2}$ on $\mathrm{GL}_2(\mathbb{R}) \times$ `finiteAdelicGL2Subgroup ℚ` is integrable for the product of `archMeasure` weighted by [`HaarQuotient.density realUnipotent μNArch`](def/HaarQuotient.html#L25) and $\mu_f$ weighted by [`HaarQuotient.density finUnipotent μNFin`](def/HaarQuotient.html#L25). (f) The function $g \mapsto W_f(\mathrm{finFactor}\,g)\bigl(W_f'(\mathrm{finFactor}\,g)F_f(\mathrm{finFactor}\,g)\bigr)\,\bigl(\mathrm{ideleNorm}(\det g)\bigr)^{s+1/2-1/2}$ on `finiteAdelicGL2Subgroup ℚ` is integrable for $\mu_f$ weighted by [`HaarQuotient.density RSCarrier.finUnipotent μNFin`](def/HaarQuotient.html#L25). (g) The function $g \mapsto W_A(g)\bigl(W_A'(g)\exp(-\pi(g_{10}^2+g_{11}^2))\bigr)\,|\det g|^{s+1/2-1/2}$ on $\mathrm{GL}_2(\mathbb{R})$ is integrable for [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) weighted by [`HaarQuotient.density realUnipotent μNArch`](def/HaarQuotient.html#L25). In (e), (f) and (g) the exponents are written as $(s-1/2+1)-1/2$ and $s+1/2-1/2$, both equal to $s$.
--
--   These are the analytic side conditions of the $\mathrm{GL}_2 \times \mathrm{GL}_2$ Rankin–Selberg unfolding over $\mathbb{Q}$: absolute convergence of the Bruhat series of the Godement section on the truncated fundamental domain $D$, integrability of the folded and of the unfolded integrands, and integrability of the archimedean and finite factors separately, all valid on a right half-plane. They are supplied in exactly the form required by [`AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat`](thm.html#AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat), where the global integral of the Godement–Eisenstein series against $\varphi\varphi'$ is identified with the Whittaker integral and with an Euler product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat
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
    (∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) *
          whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) =
        whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g *
          whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g) ∧
    ∃ σd : ℝ, ∀ s : ℂ, σd < s.re →
      ∀ (ν₀ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [ν₀.IsHaarMeasure]
        (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
        (μNArch : Measure realUnipotent) [μNArch.IsHaarMeasure]
        (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
      Measurable (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
          whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g *
            whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g *
            rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) g) ∧
      (∀ g ∈ D, Summable fun ξ : ℚ =>
        ‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2)
          (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ) * g)‖) ∧
      IntegrableOn (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ‖φ g * φ' g‖ *
          (‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) g‖ +
            ∑' ξ : ℚ, ‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2)
              (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ) * g)‖))
        D (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) ∧
      Integrable (fun q : UnipotentQuotient ℚ =>
          ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 q.out *
            whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 q.out *
            rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) q.out‖)
        (unipotentQuotientMeasure ℚ) ∧
      Integrable (fun p : GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ =>
          ((WA p.1 * (WA' p.1 * FA p.1)) *
              (((|(Matrix.GeneralLinearGroup.det p.1 : ℝ)| : ℝ) : ℂ) ^ ((s - 1 / 2 + 1) - 1 / 2))) *
            ((Wf p.2 * (Wf' p.2 * Ff p.2)) *
              ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ)
                ^ ((s - 1 / 2 + 1) - 1 / 2))))
        ((archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)).prod
          (μf.withDensity (HaarQuotient.density finUnipotent μNFin))) ∧
      Integrable
        (fun g : finiteAdelicGL2Subgroup ℚ => (Wf (finFactor g) * (Wf' (finFactor g) * Ff (finFactor g))) *
          ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) ∧
      Integrable
        (fun g : GL (Fin 2) ℝ =>
          (WA g * (WA' g * Complex.exp (-(Real.pi *
              (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
            (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)) := by sorry
