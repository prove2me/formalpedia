-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/516d861b-92e1-5ca0-b433-3a5d6d81640e
-- title:
--   Integrability of the archimedean Rankin–Selberg integrand over ℚ
-- statement:
--   The data are: real parameters $c,u,d_1,d_2$; a finite set $T$ of elements of $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ and a finite set $S$ of finite places of $\mathbb{Q}$; two functions $\varphi,\varphi'$ on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with values in $\mathbb{C}$; three functions $W_\infty, W'_\infty, F_\infty$ (`WA`, `WA'`, `FA`) on $\mathrm{GL}_2(\mathbb{R})$ and three functions $W_f, W'_f, F_f$ (`Wf`, `Wf'`, `Ff`) on `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean projection `glArch`; a function $\Phi$ on $\mathbb{A}_{\mathbb{Q}}^2$; a real-valued torus profile $P$ together with an abscissa $x_0$; a set $D$ of adelic matrices; real numbers $e_1,e_2,c_S,u_S$ and a finite set $t_S$ of adelic matrices.
--
--   The automorphy group of hypotheses asks that $\varphi$ and $\varphi'$ be continuous, that each satisfy `IsRapidlyDecreasingOnSiegelSets ℚ`, i.e. for all $c,u$, every adelic $t$ and $c>0$, and every $N\in\mathbb{N}$ there is a constant $C$ with $\|\varphi(gt)\|\,(1+\mathrm{archHeight}(g_\infty))^N\le C$ for $g$ in the integral windowed Siegel set of parameters $c,u$ (finite part in `finiteIntegralGL2`, archimedean height at least $c$, and $\mathrm{xWindowSq}\le u^2$ at every infinite place), and that both be left invariant under the global points $\mathrm{GL}_2(\mathbb{Q})$ embedded diagonally. The Schwartz–Bruhat hypothesis asks $\Phi\in$ `schwartzBruhat2 ℚ`, the $\mathbb{C}$-span of pure tensors of a Schwartz function on the mixed space with a locally constant compactly supported function on $\mathbb{A}_{\mathrm{fin}}^2$.
--
--   The fundamental-domain group of hypotheses requires $0<e_1<e_2$, $0<c_S$, that $D$ be measurable with finite adelic Haar volume `adelicGLHaar`, that on $D$ the idele norm of the determinant lie in $[e_1,e_2]$, and that $D$ be contained in the union over $t\in t_S$ of the right translates by $t$ of the integral windowed Siegel set of parameters $c_S,u_S$.
--
--   The factorisation group of hypotheses concerns the Whittaker coefficients taken with respect to the carrier data `productionPinsOf ℚ` built from the domain $\bigcup_{x\in T}(\,\cdot\,x)$-translates of the centre-cut Siegel set `centreCutSiegelSet ℚ c u d₁ d₂` (finite part integral, `localHeight` $\ge c$, `xWindowSq` $\le u^2$ and `archDetNorm` in $[d_1,d_2]$ at every infinite place), the level subgroups $N\mapsto$ `levelOne ⊓ finiteAdelicGL2Subgroup ℚ`, the Hecke generators `heckeGen`, and the box `adelicBox ℚ`; for these data the relevant ingredient of the coefficient is the additive measure, namely adelic additive Haar measure conditioned on `adelicBox ℚ`, and the coefficient of a function $\phi$ at $\alpha$ and $g$ is $\int \phi(n(x)g)\psi(-\alpha x)$. It is required that for every $g$ the coefficient of $\varphi$ at $\alpha=1$ with respect to the standard character `psiQ` equal $W_\infty(\mathrm{ratArchGL2}\,g)\,W_f(\mathrm{finFactor}\,g)$, and that the coefficient of $\varphi'$ at $\alpha=1$ with respect to `psiQ`$^{-1}$ equal $W'_\infty(\mathrm{ratArchGL2}\,g)\,W'_f(\mathrm{finFactor}\,g)$, where `ratArchGL2` is the real archimedean component and `finFactor` the complementary finite factor. Likewise $\Phi$ evaluated at the bottom row of $g$ (the vector $j\mapsto g_{1j}$) is required to equal $F_\infty(\mathrm{ratArchGL2}\,g)\,F_f(\mathrm{finFactor}\,g)$, and $F_\infty$ to be the Gaussian $F_\infty(g)=\exp(-\pi(g_{10}^2+g_{11}^2))$.
--
--   The torus group of hypotheses requires that for all real $a_1\neq 0$ and $a_2>0$ one have $W_\infty(h)W'_\infty(h)=P(a_1/a_2)$ for $h=$ `upperUnit` $a_1\,0\,a_2$, the upper triangular matrix $\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$, that $P\ge 0$ pointwise, and that $y\mapsto P(y)|y|^{\sigma'-2}$ be integrable on $\mathbb{R}$ for every $\sigma'>x_0$.
--
--   The measurability and invariance group of hypotheses requires $W_f$, $W'_f$, $F_f$ measurable, and (hypothesis `_harch`, five clauses) that $W_\infty$ and $W'_\infty$ be Borel measurable on $\mathrm{GL}_2(\mathbb{R})$ and $P$ measurable, that the product $W_\infty W'_\infty$ be invariant under left translation by the unipotent subgroup `realUnipotent` (the range of the homomorphism $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$ over $\mathbb{R}$), and invariant under right translation by those $\kappa'$ in `rowIsometrySubgroup ℝ` with determinant $1$.
--
--   The local data at the remaining places consist of a family $\varpi_v$ of elements of the valuation rings $\mathcal{O}_v$, with the hypothesis `hπ` that the image of $\varpi_v$ in the completion is nonzero for $v\notin S$, four complex-valued families $\lambda,\omega,\lambda',\omega'$ on finite places, and a real exponent $\kappa$. The hypothesis `_hfin` (seven clauses) requires: $\varpi_v$ to be a uniformiser for $v\notin S$, in the sense that its valuation is $\exp(-1)$; the bounds $\|\lambda_v\|,\|\omega_v\|,\|\lambda'_v\|,\|\omega'_v\|\le (\mathrm{absNorm}\,v)^{\kappa}$ for $v\notin S$; invariance of the product $W_f\cdot(W'_f\cdot F_f)$ under left translation by `finUnipotent`; for each $v\notin S$ the existence of an additive character $\psi$ of the completion at $v$, trivial on $\mathcal{O}_v$ but nontrivial on some $r/\varpi_v$ with $r\in\mathcal{O}_v$, such that left translation of $W_f$ by the unipotent $n(x)$ at $v$ multiplies it by $\psi(x)$; right invariance of $W_f$, and of the product $W'_f\cdot F_f$, under `localLevelOne (𝓞 ℚ) ℚ v ⊤` at every $v\notin S$; and the unramified torus law: for $v\notin S$, for every $g$ whose component at $v$ is trivial and all integers $m,n$, the value of $W_f\cdot(W'_f\cdot F_f)$ at $g$ right translated at $v$ by $\mathrm{diag}(\varpi_v^m,1)\cdot\mathrm{diag}(\varpi_v,\varpi_v)^n$ equals $(\omega_v\omega'_v)^{n}\,\mathrm{heckeRecursionSeq}(N_v,\lambda_v,\omega_v)(m)\,\mathrm{heckeRecursionSeq}(N_v,\lambda'_v,\omega'_v)(m)$ times its value at $g$ when $m,n\ge 0$, and $0$ otherwise, where $N_v$ is the absolute norm of $v$ and `heckeRecursionSeq` is the sequence given by $a_0=1$, $a_1=\lambda/N$, $a_{m+2}=(\lambda a_{m+1}-\omega a_m)/N$.
--
--   The support hypothesis `_hsupp` requires the existence of a compact set $\mathrm{Cpt}$ in `finiteAdelicGL2Subgroup ℚ` and a real bound $B_0$ such that $\|W_f(g)\,(W'_f(g)\,F_f(g))\|\le B_0$ for all $g$, and such that whenever $g$ admits at every $v\notin S$ a factorisation $n'k'$ with $n'$ in the range of the unipotent homomorphism over the completion at $v$ and $k'$ in `localLevelOne (𝓞 ℚ) ℚ v ⊤`, and $W_f(g)(W'_f(g)F_f(g))\neq 0$, there are $n$ in `finUnipotent` and $h\in\mathrm{Cpt}$ whose components agree with those of $ng$ at every $v\in S$.
--
--   Conclusion. With $\mathrm{GL}_2(\mathbb{R})$ given its Borel structure, there exists $\sigma_d\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\operatorname{Re}s>\sigma_d$ and every choice of Haar measures $\nu_0$ on the idele group $(\mathbb{A}_{\mathbb{Q}})^{\times}$, $\mu_f$ on `finiteAdelicGL2Subgroup ℚ`, $\mu_{N,\infty}$ on `realUnipotent` and $\mu_{N,\mathrm{fin}}$ on `finUnipotent`, the function
--   $$g\longmapsto \bigl(W_\infty(g)\,\bigl(W'_\infty(g)\,e^{-\pi(g_{10}^2+g_{11}^2)}\bigr)\bigr)\cdot\bigl(|\det g|\bigr)^{\,s+1/2-1/2}$$
--   is integrable on $\mathrm{GL}_2(\mathbb{R})$ with respect to [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) weighted by the density [`HaarQuotient.density realUnipotent`](def/HaarQuotient.html#L25) $\mu_{N,\infty}$; here `archMeasure` is Lebesgue measure on $2\times 2$ real matrices pulled back to $\mathrm{GL}_2(\mathbb{R})$ with density $|\det g|^{-2}$, the exponent is the complex power of the real absolute value of the determinant, written in the unsimplified form $s+1/2-1/2$, and the Gaussian factor is written out rather than referred to as $F_\infty$. The measures $\nu_0$, $\mu_f$ and $\mu_{N,\mathrm{fin}}$ are quantified over but do not occur in the integrand or in the measure.
--
--   This is the archimedean integrability clause of the package of side conditions for the Rankin–Selberg convolution over $\mathbb{Q}$: it asserts convergence, for $\operatorname{Re}s$ large, of the local archimedean integral of the product of the two Whittaker factors against the Gaussian Godement section and $|\det|^{s}$, on the quotient measure attached to the unipotent subgroup. It is used by the assembled side-conditions statement over $\mathbb{Q}$ and by the statements on the global Rankin–Selberg integrand and on the product of archimedean and finite Whittaker factors, and it is proved from the Iwasawa-type majorant for integrals against `archMeasure` weighted by the unipotent Haar density.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat
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
        (fun g : GL (Fin 2) ℝ =>
          (WA g * (WA' g * Complex.exp (-(Real.pi *
              (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
            (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)) := by sorry
