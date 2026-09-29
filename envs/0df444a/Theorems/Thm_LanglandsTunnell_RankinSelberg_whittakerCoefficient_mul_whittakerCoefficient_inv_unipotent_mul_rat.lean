-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat
-- name    : LanglandsTunnell.RankinSelberg.whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/6cb46898-37ad-58e9-95c5-1a1d63614c2b
-- title:
--   Unipotent invariance of a product of two Whittaker coefficients
-- statement:
--   The setting is $\mathbb{Q}$ with its ring of integers $\mathcal{O}_{\mathbb{Q}}$, and the group $\mathrm{GL}_2$ of the adele ring, written `AdelicGL2 (𝓞 ℚ) ℚ`. Throughout, the Whittaker coefficient used is the one attached to the carrier data `productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)`: this packages the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A})$, the set $\bigcup_{x\in T}(\,\cdot\,x)(\text{centreCutSiegelSet }\mathbb{Q}\,c\,u\,d_1\,d_2)$ of right translates of the set of $g$ whose finite part is integral, whose local heights at all infinite places are $\ge c$, whose window quantities `xWindowSq` are $\le u^2$ and whose archimedean determinant norms lie in $[d_1,d_2]$, the full subgroup of ideles as centre, the level subgroups $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}(v)$, and the Borel $\sigma$-algebra on $\mathbb{A}$ together with the additive Haar measure conditioned on the box `adelicBox ℚ`. Only the last of these enters the coefficient: by definition, $\mathrm{whittakerCoefficient}\,\mathbb{Q}\,\mathrm{pins}\,\psi\,\varphi\,\alpha\,g=\int \varphi\big(n(x)g\big)\,\psi\big(-(\alpha x)\big)\,d\nu(x)$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\nu$ is that conditioned Haar measure on $\mathbb{A}$. The characters used are the standard global additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615) of $\mathbb{A}_{\mathbb{Q}}$ and its inverse, and the parameter $\alpha$ is $1$.
--
--   The data are: real numbers $c,u,d_1,d_2$; a finite set $T$ of adelic matrices; a finite set $S$ of finite places of $\mathbb{Q}$; functions $\varphi,\varphi':\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$; functions $W_A,W_A',F_A:\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ and $W_f,W_f',F_f$ on the finite part $\ker(\mathrm{glArch})$; a function $\Phi$ on $\mathbb{A}^2$; a function $P:\mathbb{R}\to\mathbb{R}$ and a real $x_0$; a set $D\subseteq\mathrm{GL}_2(\mathbb{A})$, reals $e_1,e_2,c_S,u_S$ and a finite set $t_S$ of adelic matrices.
--
--   The hypotheses, grouped, are the following. (i) Analytic hypotheses on the two test vectors: $\varphi$ and $\varphi'$ are continuous, both satisfy `IsRapidlyDecreasingOnSiegelSets ℚ` (for every $c,u$, every translate $t$ and every $N$ there is a bound $C$ with $\|\varphi(gt)\|(1+\mathrm{archHeight}(g))^N\le C$ on the integral windowed Siegel set of parameters $c,u$), and both are left invariant under the global points $\mathrm{GL}_2(\mathbb{Q})$. (ii) $\Phi$ lies in the Schwartz–Bruhat space `schwartzBruhat2 ℚ`, the $\mathbb{C}$-span of products of a Schwartz function in the archimedean variables with a locally constant, compactly supported function in the finite variables. (iii) Hypotheses on the slab $D$: $0<e_1<e_2$, $0<c_S$, $D$ is measurable of finite adelic Haar measure, the idele norm of $\det$ takes values in $[e_1,e_2]$ on $D$, and $D$ is contained in the union of the right translates by $t\in t_S$ of the integral windowed Siegel set of parameters $c_S,u_S$. (iv) Factorisation hypotheses: the $\psi_{\mathbb{Q}}$-Whittaker coefficient of $\varphi$ at $1$ equals $W_A(\mathrm{ratArchGL2}\,g)\,W_f(\mathrm{finFactor}\,g)$ for all $g$, the $\psi_{\mathbb{Q}}^{-1}$-Whittaker coefficient of $\varphi'$ at $1$ equals $W_A'(\mathrm{ratArchGL2}\,g)\,W_f'(\mathrm{finFactor}\,g)$, and $\Phi(\mathrm{bottomRowVec}\,\mathbb{Q}\,g\,1)=F_A(\mathrm{ratArchGL2}\,g)\,F_f(\mathrm{finFactor}\,g)$, with $F_A(g)=\exp\!\big(-\pi(g_{10}^2+g_{11}^2)\big)$. (v) Torus profile hypotheses: $W_A\big(\mathrm{upperUnit}\,a_1\,0\,a_2\big)\,W_A'\big(\mathrm{upperUnit}\,a_1\,0\,a_2\big)=P(a_1/a_2)$ for $a_1\ne0$ and $a_2>0$; $P\ge0$; and $y\mapsto P(y)|y|^{\sigma'-2}$ is integrable for every $\sigma'>x_0$. (vi) Measurability and invariance at the archimedean place: $W_f,W_f',F_f$ are measurable, and `_harch` asserts that $W_A$ and $W_A'$ are Borel measurable, that $P$ is measurable, that $W_A\,W_A'$ is invariant under left translation by the image of $\mathrm{unipotentGL2Hom}$ in $\mathrm{GL}_2(\mathbb{R})$, and that $W_A\,W_A'$ is invariant under right translation by elements of the row-isometry subgroup of determinant $1$. (vii) Local uniformiser data: a family $\varpi$ of elements $\varpi_v\in\mathcal{O}_v$, with $h\pi$ asserting that the image of $\varpi_v$ in the completion is nonzero for $v\notin S$; complex-valued families $\lambda,\omega,\lambda',\omega'$ on the finite places and a real $\kappa$. (viii) The hypothesis `_hfin` (seven clauses, summarised here): for $v\notin S$ the valuation of $\varpi_v$ is $\exp(-1)$, so $\varpi_v$ is a uniformiser; the four Hecke parameters satisfy $\|\lambda_v\|,\|\omega_v\|,\|\lambda'_v\|,\|\omega'_v\|\le N(v)^{\kappa}$ off $S$; the product $W_f\,(W_f'\,F_f)$ is invariant under left translation by [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); for each $v\notin S$ there is an additive character $\psi_v$ of the completion, trivial on $\mathcal{O}_v$ and nontrivial on $\varpi_v^{-1}\mathcal{O}_v$, such that $W_f$ transforms by $\psi_v(x)$ under left translation by the local unipotent $\mathrm{unipotent}(x)$ embedded at $v$; $W_f$ is right invariant under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) at each $v\notin S$, and so is the product $W_f'\,F_f$; and for $v\notin S$, $g$ with trivial component at $v$ and integers $m,n$, the value of $W_f\,(W_f'\,F_f)$ at $g$ right translated by the embedded local element $\mathrm{diagZ}(\varpi_v)^{\,m}\cdot\mathrm{scalarPi}(\varpi_v)^{\,n}$ equals $\big(\omega_v\omega'_v\big)^{n}\,\mathrm{heckeRecursionSeq}\,N(v)\,\lambda_v\,\omega_v\,m\cdot \mathrm{heckeRecursionSeq}\,N(v)\,\lambda'_v\,\omega'_v\,m$ times the value at $g$ when $0\le m$ and $0\le n$, and $0$ otherwise. (ix) The hypothesis `_hsupp`: there exist a compact set $\mathrm{Cpt}$ in the finite part and a bound $B_0$ such that $\|W_f\,(W_f'\,F_f)\|\le B_0$ everywhere, and such that whenever $g$ has, at every $v\notin S$, local component of the form (local unipotent)·(element of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178)) and $W_f(g)\,(W_f'(g)\,F_f(g))\ne0$, there are $n$ in [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h\in\mathrm{Cpt}$ with the same local components as $n\,g$ at every $v\in S$.
--
--   The conclusion, stated after fixing the Borel $\sigma$-algebra on $\mathrm{GL}_2(\mathbb{R})$, is a single identity: for every $n$ in the adelic unipotent subgroup `adelicUnipotent ℚ` (the image of $\mathrm{unipotentGL2Hom}$ over $\mathbb{A}$) and every $g\in\mathrm{GL}_2(\mathbb{A})$, the product of the $\psi_{\mathbb{Q}}$-Whittaker coefficient of $\varphi$ at $\alpha=1$ and the $\psi_{\mathbb{Q}}^{-1}$-Whittaker coefficient of $\varphi'$ at $\alpha=1$, both with respect to the above carrier data and both evaluated at $n\,g$, equals the same product evaluated at $g$.
--
--   This is the left $N(\mathbb{A})$-invariance of the product of a $\psi$-Whittaker coefficient and a $\psi^{-1}$-Whittaker coefficient, the statement that makes the Rankin–Selberg integrand over $\mathbb{Q}$ descend to the unipotent quotient. It is one conjunct of the package of side conditions for the Rankin–Selberg construction over $\mathbb{Q}$, and is used in the construction of the integrable kernel on the unipotent quotient and in the assembly of those side conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat.lean

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

theorem LanglandsTunnell.RankinSelberg.whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat
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
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g) := by sorry
