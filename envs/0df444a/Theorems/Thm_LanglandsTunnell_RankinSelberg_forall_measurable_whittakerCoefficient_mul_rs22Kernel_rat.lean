-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_measurable_whittakerCoefficient_mul_rs22Kernel_rat
-- name    : LanglandsTunnell.RankinSelberg.forall_measurable_whittakerCoefficient_mul_rs22Kernel_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/7291275b-dac6-5982-a568-5333dff2ff6f
-- title:
--   Measurability of the unfolded Rankin–Selberg integrand over ℚ
-- statement:
--   The ambient group is $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, written `AdelicGL2 (𝓞 ℚ) ℚ`, carrying the Borel $\sigma$-algebra `glBorel` attached to its topology; `finiteAdelicGL2Subgroup ℚ` is the kernel of the archimedean-component homomorphism `glArch`, `ratArchGL2 g` $\in \mathrm{GL}_2(\mathbb{R})$ is the component of $g$ at the unique infinite place of $\mathbb{Q}$ transported along $\mathbb{Q}_\infty \cong \mathbb{R}$, and `finFactor g` is the element $\mathrm{archRealGLAt}(\mathrm{ratArchGL2}\,g)^{-1} g$ of that kernel.
--
--   The data are real numbers $c, u, d_1, d_2$, a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, a finite set $S$ of finite places of $\mathbb{Q}$, functions $\varphi, \varphi' : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$, functions $W_A, W_A', F_A : \mathrm{GL}_2(\mathbb{R}) \to \mathbb{C}$ and $W_f, W_f', F_f$ on `finiteAdelicGL2Subgroup ℚ`, a function $\Phi : \mathbb{A}_{\mathbb{Q}}^2 \to \mathbb{C}$, a function $P : \mathbb{R} \to \mathbb{R}$ with a real number $x_0$, a subset $D \subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, real numbers $e_1, e_2, c_S, u_S$ and a finite set $t_S$ of adelic matrices.
--
--   Throughout, the two Whittaker coefficients are those formed with the `CarrierPins` package `productionPinsOf ℚ` whose domain field is $\bigcup_{x \in T} (\cdot * x)''\,$`centreCutSiegelSet ℚ c u d₁ d₂` (the set of $g$ whose finite part is integral, whose local height at every infinite place is at least $c$, whose window quantity `xWindowSq` at every infinite place is at most $u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$), whose level field is $N \mapsto$ `levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ`, whose generators are the Hecke elements `heckeGen (𝓞 ℚ) ℚ v`, and whose additive measure is the adelic additive Haar measure conditioned on the box `adelicBox ℚ`. Of this package only the latter measure enters, so
--   $$\mathrm{whittakerCoefficient}\,\psi\,\phi\,1\,(g) = \int_{\mathbb{A}_{\mathbb{Q}}} \phi\bigl(\mathrm{unipotentGL2}(x)\, g\bigr)\, \psi(-x)\, d\nu(x),$$
--   with $\nu$ the normalised restriction of additive Haar measure to `adelicBox ℚ`; the characters used are the standard additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615) of $\mathbb{A}_{\mathbb{Q}}$ and its inverse. Likewise `rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1/2) g` is the product of the trivial central character at $\det g$, of $\bigl(\mathrm{moduleChar}(\det g)\bigr)^{(s-1/2)+1/2}$ (the real module character of the idele $\det g$, raised to a complex power), and of $\Phi$ evaluated at `bottomRowVec ℚ g 1`, the bottom row of $g$.
--
--   The hypotheses fall into the following groups.
--
--   Automorphy and decay: `_hφc`, `_hφ'c` assert continuity of $\varphi$ and $\varphi'$; `_hφd`, `_hφ'd` assert `IsRapidlyDecreasingOnSiegelSets ℚ` for both, that is, for all $c, u$, all adelic $t$ with $c > 0$ and all $N$ there is a constant bounding $\|\varphi(g t)\| (1 + \mathrm{archHeight}(\mathrm{glArch}\,g))^N$ on `integralWindowedSiegelSet ℚ c u`; `_hφG`, `_hφ'G` assert left invariance under the image of $\mathrm{GL}_2(\mathbb{Q})$ under `globalPoints`; `_hΦ` asserts that $\Phi$ lies in `schwartzBruhat2 ℚ`, the $\mathbb{C}$-span of pure tensors of a Schwartz function at infinity with a locally constant compactly supported function on the finite adeles.
--
--   Domain data: $0 < e_1 < e_2$ and $0 < c_S$; $D$ is measurable and of finite adelic Haar measure; $D$ is contained in the slab where the idele norm `TateGlobal.ideleNorm` of $\det g$ lies in $[e_1, e_2]$, and in the union of the right translates $(\cdot * t)''$`integralWindowedSiegelSet ℚ cS uS` over $t \in t_S$.
--
--   Factorisation: `_hW` and `_hW'` state that the Whittaker coefficient of $\varphi$ at `psiQ` and that of $\varphi'$ at `psiQ⁻¹` (both at $\alpha = 1$) factor as $W_A(\mathrm{ratArchGL2}\,g)\,W_f(\mathrm{finFactor}\,g)$ and $W_A'(\mathrm{ratArchGL2}\,g)\,W_f'(\mathrm{finFactor}\,g)$; `_hΦsplit` states the analogous splitting $\Phi(\mathrm{bottomRowVec}\,g\,1) = F_A(\mathrm{ratArchGL2}\,g)\,F_f(\mathrm{finFactor}\,g)$; `_hFA` fixes the archimedean factor to be the Gaussian $F_A(g) = \exp(-\pi(g_{10}^2 + g_{11}^2))$.
--
--   Torus profile: `_hT` states that on the upper triangular elements `upperUnit a₁ 0 a₂` with $a_1 \neq 0$ and $a_2 > 0$ the product $W_A W_A'$ equals the real number $P(a_1/a_2)$; `_hP0` that $P \geq 0$; `_hPint` that $y \mapsto P(y)\,|y|^{\sigma'-2}$ is integrable for every $\sigma' > x_0$.
--
--   Measurability and invariance of the factors: `_hWfm`, `_hWf'm`, `_hFfm` assert measurability of $W_f, W_f', F_f$; the five conjuncts of `_harch` assert Borel measurability of $W_A$ and $W_A'$ on $\mathrm{GL}_2(\mathbb{R})$, measurability of $P$, invariance of the product $W_A W_A'$ under left multiplication by elements of `realUnipotent` (the image of `unipotentGL2Hom` over $\mathbb{R}$), and its invariance under right multiplication by elements of `rowIsometrySubgroup ℝ` of determinant $1$.
--
--   Local data off $S$: a family $\varpi$ of elements of the valuation rings $\mathcal{O}_v$, with `hπ` asserting that the image of $\varpi_v$ in the completion is nonzero for $v \notin S$; families $\mathrm{lam}, \mathrm{om}, \mathrm{lam}', \mathrm{om}'$ of complex numbers indexed by the finite places; and a real number $\kappa$. The hypothesis `_hfin` (seven clauses) requires: for $v \notin S$ that $\varpi_v$ is a uniformiser, its valuation being $\exp(-1)$; for $v \notin S$ the bounds $\|\mathrm{lam}_v\|, \|\mathrm{om}_v\|, \|\mathrm{lam}'_v\|, \|\mathrm{om}'_v\| \leq (\mathrm{absNorm}\,v)^\kappa$; invariance of the product $W_f \cdot (W_f' \cdot F_f)$ under left multiplication by elements of [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); for $v \notin S$ the existence of an additive character $\psi$ of the completion at $v$ that is trivial on the valuation ring, nontrivial at some $r/\varpi_v$ with $r$ integral, and satisfies $W_f(\mathrm{finFactor}(\mathrm{placeEmbed}\,v\,(\mathrm{unipotent}\,x) \cdot g)) = \psi(x) W_f(\mathrm{finFactor}\,g)$; for $v \notin S$ right invariance of $W_f \circ \mathrm{finFactor}$, and of the product $(W_f' \cdot F_f) \circ \mathrm{finFactor}$, under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178); and finally, for $v \notin S$, for $g$ with trivial component at $v$ and for integers $m, n$, the Hecke–torus law
--   $$(W_f W_f' F_f)\bigl(\mathrm{finFactor}(g \cdot \mathrm{placeEmbed}\,v\,(\mathrm{diagZ}(\varpi_v)\,m \cdot \mathrm{scalarPi}(\varpi_v)^n))\bigr) = \Lambda_{m,n}(v) \cdot (W_f W_f' F_f)(\mathrm{finFactor}\,g),$$
--   where $\Lambda_{m,n}(v)$ is $(\mathrm{om}_v \mathrm{om}'_v)^n\,\mathrm{heckeRecursionSeq}(N_v, \mathrm{lam}_v, \mathrm{om}_v)(m)\,\mathrm{heckeRecursionSeq}(N_v, \mathrm{lam}'_v, \mathrm{om}'_v)(m)$ when $m, n \geq 0$ and $0$ otherwise, $N_v$ being the absolute norm of $v$, $\mathrm{diagZ}(\pi)\,m = \mathrm{diag}(\pi^m, 1)$, $\mathrm{scalarPi}(\pi) = \pi I$, and `heckeRecursionSeq N lam om` the sequence with values $1$, $\mathrm{lam}/N$ and $(\mathrm{lam}\,u_{m+1} - \mathrm{om}\,u_m)/N$.
--
--   Support and boundedness: `_hsupp` requires a compact subset $\mathrm{Cpt}$ of `finiteAdelicGL2Subgroup ℚ` and a real $B_0$ such that $\|W_f(g)(W_f'(g)F_f(g))\| \leq B_0$ for all $g$, and such that for every $g$ whose component at each $v \notin S$ factors as an element of the range of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33) times an element of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), if $W_f(g)(W_f'(g)F_f(g)) \neq 0$ then there are $n$ in [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h \in \mathrm{Cpt}$ with the components of $n g$ and of $h$ equal at every $v \in S$.
--
--   Under these hypotheses, with the Borel $\sigma$-algebra installed on $\mathrm{GL}_2(\mathbb{R})$, the conclusion is: for every $s \in \mathbb{C}$ the function
--   $$g \longmapsto \mathrm{whittakerCoefficient}(\mathrm{psiQ}, \varphi, 1)(g) \cdot \mathrm{whittakerCoefficient}(\mathrm{psiQ}^{-1}, \varphi', 1)(g) \cdot \mathrm{rs22Kernel}\,\mathbb{Q}\,1\,(\mathrm{moduleChar}\,\mathbb{Q})\,\Phi\,(s - 1/2)\,(g)$$
--   is measurable on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, the Whittaker coefficients being taken literally with the `productionPinsOf` data described above rather than through their assumed factorisations.
--
--   This is the measurability side condition of the Rankin–Selberg unfolding over $\mathbb{Q}$: the integrand $W(g)W'(g)\|\det g\|^{s}\Phi(\text{bottom row of }g)$ of the global $\mathrm{GL}_2 \times \mathrm{GL}_2$ zeta integral is a measurable function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$. It is one conjunct of the package of side conditions collected in [`LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat), whose hypothesis list it repeats verbatim, and it uses the continuity of $g \mapsto \|\det g\|_{\mathbb{A}}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_measurable_whittakerCoefficient_mul_rs22Kernel_rat.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_measurable_whittakerCoefficient_mul_rs22Kernel_rat
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
    ∀ s : ℂ,
      Measurable (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
          whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g *
            whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g *
            rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) g) := by sorry
