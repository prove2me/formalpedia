-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/696747b7-5c9c-5c41-a7dc-75f28203891f
-- title:
--   Integrability of the Rankin–Selberg integrand on NbackslashGL₂(A_ℚ)
-- statement:
--   The setting is $F=\mathbb{Q}$, with $\mathrm{GL}_2$ over the adele ring $\mathbb{A}=\mathbb{A}_{\mathbb{Q}}$; the measurable structures used throughout are the Borel ones attached to the adelic and idelic topologies and to $\mathrm{GL}_2(\mathbb{A})$, and on $\mathrm{GL}_2(\mathbb{R})$ the Borel $\sigma$-algebra is installed in the conclusion.
--
--   The data are: real parameters $c,u,d_1,d_2$; a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A})$; a finite set $S$ of height-one primes of $\mathbb{Z}$; two functions $\varphi,\varphi' : \mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$; archimedean factors $W_\infty,W'_\infty,F_\infty : \mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ and finite factors $W_f,W'_f,F_f$ on the subgroup `finiteAdelicGL2Subgroup ℚ` (the kernel of the projection $\mathrm{GL}_2(\mathbb{A})\to\mathrm{GL}_2(\mathbb{A}_\infty)$); a function $\Phi$ on $\mathbb{A}^2$; a function $P:\mathbb{R}\to\mathbb{R}$ with an abscissa $x_0\in\mathbb{R}$; a set $D\subseteq\mathrm{GL}_2(\mathbb{A})$ with reals $e_1,e_2,c_S,u_S$ and a finite set $t_S$ of elements of $\mathrm{GL}_2(\mathbb{A})$; a family $\varpi$ assigning to each height-one prime $v$ an element of the valuation ring $\mathcal{O}_v$ of the completion $\mathbb{Q}_v$, subject to $h\pi$: for $v\notin S$ the image of $\varpi_v$ in $\mathbb{Q}_v$ is non-zero; families $\mathrm{lam},\mathrm{om},\mathrm{lam}',\mathrm{om}'$ of complex numbers indexed by the primes, and a real exponent $\kappa$.
--
--   The Whittaker data are taken with respect to the carrier `productionPinsOf ℚ` built from the set $\bigcup_{x\in T}\{g x : g\in \text{centreCutSiegelSet}\ \mathbb{Q}\,c\,u\,d_1\,d_2\}$, the level family $N\mapsto \text{levelOne}\ N\sqcap \text{finiteAdelicGL2Subgroup}\ \mathbb{Q}$, the Hecke generators $v\mapsto \text{heckeGen}\ v$ and the box `adelicBox ℚ`; here `centreCutSiegelSet` is the set of $g$ with integral finite part, with $c\le\text{localHeight}$ and $\text{xWindowSq}\le u^2$ at every infinite place and with $\text{archDetNorm}$ in $[d_1,d_2]$ at every infinite place, and the carrier's adelic measure is the Haar measure on $\mathrm{GL}_2(\mathbb{A})$, its additive measure the adelic Haar measure conditioned on `adelicBox ℚ`, and its central subgroup is $\top$. For an additive character $\psi$ of $\mathbb{A}$ the coefficient is $\text{whittakerCoefficient}\ \mathbb{Q}\ \text{pins}\ \psi\ \phi\ \alpha\ g=\int \phi(n(x)g)\,\psi(-\alpha x)\,d\nu(x)$, $n(x)$ the upper unipotent with entry $x$ and $\nu$ the conditioned adelic measure.
--
--   The hypotheses fall into the following groups.
--
--   Automorphy and decay: $\varphi$ and $\varphi'$ are continuous; each is rapidly decreasing on Siegel sets in the sense of `IsRapidlyDecreasingOnSiegelSets` (for all $c,u$, all $t$, all $c>0$ and all $N$ there is $C$ with $\|\phi(gt)\|(1+\text{archHeight}(g_\infty))^N\le C$ for $g$ in the integral windowed Siegel set); and each is invariant under left translation by the global points $\mathrm{GL}_2(\mathbb{Q})$.
--
--   The Schwartz–Bruhat condition: $\Phi$ lies in `schwartzBruhat2 ℚ`, the $\mathbb{C}$-span of pure tensors of a Schwartz function on the archimedean part and a locally constant compactly supported function on $(\mathbb{A}_{\mathrm{fin}})^2$.
--
--   The slab conditions on $D$: $0<e_1<e_2$, $0<c_S$, $D$ measurable of finite Haar measure, $D$ contained in the set of $g$ with idele norm of $\det g$ in $[e_1,e_2]$, and $D$ contained in $\bigcup_{t\in t_S}\{g t: g\in \text{integralWindowedSiegelSet}\ \mathbb{Q}\,c_S\,u_S\}$.
--
--   The factorisation hypotheses: for every $g$, the Whittaker coefficient of $\varphi$ at the standard character $\psi_{\mathbb{Q}}$ and $\alpha=1$ equals $W_\infty(\text{ratArchGL2}\ g)\,W_f(\text{finFactor}\ g)$, and the coefficient of $\varphi'$ at $\psi_{\mathbb{Q}}^{-1}$ equals $W'_\infty(\text{ratArchGL2}\ g)\,W'_f(\text{finFactor}\ g)$; and $\Phi$ evaluated on the bottom row of $g$ equals $F_\infty(\text{ratArchGL2}\ g)\,F_f(\text{finFactor}\ g)$. Here `ratArchGL2` is the real component at the unique infinite place and `finFactor` removes that component.
--
--   The archimedean normalisations: $F_\infty(g)=\exp(-\pi(g_{10}^2+g_{11}^2))$ for all $g\in\mathrm{GL}_2(\mathbb{R})$; on the diagonal torus, $W_\infty\,W'_\infty$ evaluated at `upperUnit a₁ 0 a₂` equals $P(a_1/a_2)$ for all $a_1\neq 0$ and $a_2>0$; $P\ge 0$ everywhere; and for every $\sigma'>x_0$ the function $y\mapsto P(y)|y|^{\sigma'-2}$ is integrable on $\mathbb{R}$.
--
--   Measurability and invariance: $W_f$, $W'_f$, $F_f$ are measurable; the conjunction `_harch` asserts that $W_\infty$ and $W'_\infty$ are Borel measurable, that $P$ is measurable, that $W_\infty W'_\infty$ is invariant under left multiplication by the real unipotent subgroup, and that it is invariant under right multiplication by elements of $\text{rowIsometrySubgroup}\ \mathbb{R}$ of determinant $1$.
--
--   The finite-place hypothesis `_hfin` (seven clauses) requires: for $v\notin S$ the element $\varpi_v$ has valuation $\exp(-1)$, so is a uniformiser; for $v\notin S$ the four eigenvalue parameters $\mathrm{lam}_v,\mathrm{om}_v,\mathrm{lam}'_v,\mathrm{om}'_v$ are bounded in absolute value by $(\mathrm{Nm}\,v)^{\kappa}$; the product $W_f W'_f F_f$ is invariant under left multiplication by the finite unipotent subgroup [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); for $v\notin S$ there is an additive character $\psi_v$ of $\mathbb{Q}_v$ trivial on $\mathcal{O}_v$, non-trivial on $\varpi_v^{-1}\mathcal{O}_v$, such that $W_f$ transforms by $\psi_v(x)$ under left multiplication by the local unipotent $n(x)$ at $v$; for $v\notin S$ the function $W_f$ is right invariant under $\text{localLevelOne}\ v\ \top$ (the preimage of the finite level-one subgroup under the local embedding at $v$), and likewise the product $W'_f F_f$ is right invariant under that subgroup; and finally, an unramified torus law: for $v\notin S$, for $g$ with trivial local component at $v$ and integers $m,n$, the product $W_f W'_f F_f$ evaluated at $g$ multiplied on the right by the image at $v$ of $\text{diagZ}(\varpi_v)^{\phantom{}}$ at exponent $m$ times $\text{scalarPi}(\varpi_v)^n$ equals $(\mathrm{om}_v\,\mathrm{om}'_v)^{n}\,\text{heckeRecursionSeq}(\mathrm{Nm}\,v,\mathrm{lam}_v,\mathrm{om}_v)(m)\,\text{heckeRecursionSeq}(\mathrm{Nm}\,v,\mathrm{lam}'_v,\mathrm{om}'_v)(m)$ times $W_f(g)W'_f(g)F_f(g)$ when $m,n\ge 0$, and $0$ otherwise; `heckeRecursionSeq` is the sequence with values $1$, $\mathrm{lam}/N$ and $(\mathrm{lam}\,a_{m+1}-\mathrm{om}\,a_m)/N$.
--
--   The support hypothesis `_hsupp` asserts the existence of a compact set $\mathrm{Cpt}$ in `finiteAdelicGL2Subgroup ℚ` and a bound $B_0$ such that $\|W_f(g)W'_f(g)F_f(g)\|\le B_0$ for all $g$, and such that for every $g$ whose local component at each $v\notin S$ factors as a unipotent times an element of $\text{localLevelOne}\ v\ \top$, non-vanishing of $W_f(g)W'_f(g)F_f(g)$ implies the existence of a finite unipotent element $n$ and of $h\in\mathrm{Cpt}$ with the same local components as $n g$ at all $v\in S$.
--
--   Conclusion. There exists $\sigma_d\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\sigma_d<\operatorname{Re} s$, and for every choice of Haar measures $\nu_0$ on the idele group $\mathbb{A}^{\times}$, $\mu_f$ on `finiteAdelicGL2Subgroup ℚ`, $\mu_{N,\infty}$ on the real unipotent subgroup and $\mu_{N,\mathrm{fin}}$ on the finite unipotent subgroup, the function on the quotient $\text{UnipotentQuotient}\ \mathbb{Q}$ — the orbit quotient of $\mathrm{GL}_2(\mathbb{A})$ by the adelic unipotent subgroup — given by
--   $$q\mapsto \bigl\| W(q_{\mathrm{out}})\,W'(q_{\mathrm{out}})\,\text{rs22Kernel}\ \mathbb{Q}\ 1\ (\text{moduleChar}\ \mathbb{Q})\ \Phi\ (s-\tfrac12)\ (q_{\mathrm{out}}) \bigr\|$$
--   is integrable with respect to `unipotentQuotientMeasure ℚ`. Here $W$ and $W'$ are the two Whittaker coefficients described above (at $\psi_{\mathbb{Q}}$ for $\varphi$ and at $\psi_{\mathbb{Q}}^{-1}$ for $\varphi'$, both at $\alpha=1$), $q_{\mathrm{out}}$ is a chosen representative of the orbit $q$, `rs22Kernel` at the trivial character $1$, the module character and the parameter $s-\tfrac12$ is $|\det g|^{\,s}$ in the sense of `cpowChar` applied to $\det g$ times $\Phi$ of the bottom row of $g$, and `unipotentQuotientMeasure ℚ` is the quotient measure obtained from the Haar measure of $\mathrm{GL}_2(\mathbb{A})$ and the normalised Haar measure `unipotentHaar ℚ` of the adelic unipotent subgroup.
--
--   This is the absolute-convergence side condition for the Rankin–Selberg integral of a pair of Whittaker functions against a Godement section: after unfolding, the global integral is taken over $N_2(\mathbb{A})\backslash\mathrm{GL}_2(\mathbb{A})$, and the statement provides a half-plane $\operatorname{Re} s>\sigma_d$ on which the integrand is absolutely integrable there. It is one of the conjuncts used by [`LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat), which assembles the side conditions for the Rankin–Selberg package over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat
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
      Integrable (fun q : UnipotentQuotient ℚ =>
          ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 q.out *
            whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 q.out *
            rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) q.out‖)
        (unipotentQuotientMeasure ℚ) := by sorry
