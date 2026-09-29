-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_summable_norm_godementSection_bruhat_one_one_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/49f3ed13-6af0-541b-906f-913baf5f529b
-- title:
--   Absolute convergence of the Bruhat series of a Godement section
-- statement:
--   The data are: real parameters $c,u,d_1,d_2$; a finite set $T$ of points of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ (written `AdelicGL2 (𝓞 ℚ) ℚ`); a finite set $S$ of finite places of $\mathbb{Q}$; two functions $\varphi,\varphi'$ on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with values in $\mathbb{C}$; three functions $W_A,W_A',F_A$ on $\mathrm{GL}_2(\mathbb{R})$ and three functions $W_f,W_f',F_f$ on the subgroup `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection `glArch`); a function $\Phi$ on $\mathbb{A}_{\mathbb{Q}}^2$; a function $P$ on $\mathbb{R}$ and a real abscissa $x_0$; a set $D\subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$; reals $e_1,e_2,c_S,u_S$ and a finite set $t_S$ of points of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$.
--
--   The hypotheses fall into the following groups. *Automorphy and decay of the test vectors*: $\varphi$ and $\varphi'$ are continuous, satisfy `IsRapidlyDecreasingOnSiegelSets ℚ` (for all $c,u$, all translating elements $t$, all $c>0$ and all $N\in\mathbb{N}$ there is a bound $C$ with $\|\varphi(gt)\|\,(1+\mathrm{archHeight}(g))^N\le C$ for every $g$ in the integral windowed Siegel set of parameters $c,u$), and are invariant under left translation by the image of $\mathrm{GL}_2(\mathbb{Q})$ under `globalPoints`. *Schwartz–Bruhat condition*: $\Phi$ lies in `schwartzBruhat2 ℚ`, the $\mathbb{C}$-span of the pure tensors $g\otimes h$ with $g$ Schwartz on the mixed space and $h$ locally constant of compact support on $(\mathbb{A}^{\mathrm{fin}})^2$. *The domain $D$*: $0<e_1<e_2$, $0<c_S$, $D$ is measurable with finite measure for the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ`, $D$ is contained in the slab where the idele norm of the determinant lies in $[e_1,e_2]$, and $D$ is covered by the finitely many right translates $(\cdot\, t)$ of the integral windowed Siegel set of parameters $c_S,u_S$ for $t\in t_S$. *Factorisation of the Whittaker and Schwartz data*: for every $g$, the Whittaker coefficient at $\alpha=1$ of $\varphi$ against the standard adelic additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615), namely $\int \varphi(n(x)g)\,\psi(-x)\,d\nu$ taken with respect to the carrier data `productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)` (whose measure component is the adelic additive Haar measure conditioned on the box `adelicBox ℚ`), equals $W_A(\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{finFactor}\,g)$, where `ratArchGL2` is the real component of $g$ at the unique infinite place and `finFactor` its complementary finite part; the same for $\varphi'$ with the inverse character $\psi^{-1}$, giving $W_A'\cdot W_f'$; $\Phi$ evaluated on the bottom row of $g$ (that is, `bottomRowVec ℚ g 1`) equals $F_A(\mathrm{ratArchGL2}\,g)\cdot F_f(\mathrm{finFactor}\,g)$; $F_A$ is the Gaussian $F_A(g)=\exp\bigl(-\pi\,(g_{10}^2+g_{11}^2)\bigr)$; for $a_1\neq 0$ and $a_2>0$ the product $W_A W_A'$ at `upperUnit a₁ 0 a₂` (the matrix $\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$ viewed in $\mathrm{GL}_2(\mathbb{R})$) equals the real number $P(a_1/a_2)$; $P\ge 0$; and for every $\sigma'>x_0$ the function $y\mapsto P(y)|y|^{\sigma'-2}$ is integrable on $\mathbb{R}$. *Measurability*: $W_f,W_f',F_f$ are measurable, and the hypothesis `_harch` asserts that $W_A$ and $W_A'$ are measurable for the Borel structure on $\mathrm{GL}_2(\mathbb{R})$, that $P$ is measurable, and that the product $W_AW_A'$ is invariant under left translation by elements of `realUnipotent` (the image of the real unipotent homomorphism) and under right translation by elements of `rowIsometrySubgroup ℝ` of determinant $1$.
--
--   *Local data away from and at $S$*: a family $\varpi$ assigning to each finite place $v$ an element of the valuation ring $\mathcal{O}_v$, together with $h\pi$, which states that the image of $\varpi_v$ in the completion is non-zero for $v\notin S$; complex-valued families $\mathrm{lam},\mathrm{om},\mathrm{lam}',\mathrm{om}'$ on the finite places and a real exponent $\kappa$. The hypothesis `_hfin` has seven clauses: (i) for $v\notin S$ the valuation of $\varpi_v$ is $\exp(-1)$, so $\varpi_v$ is a uniformiser; (ii) for $v\notin S$ each of $\|\mathrm{lam}_v\|,\|\mathrm{om}_v\|,\|\mathrm{lam}'_v\|,\|\mathrm{om}'_v\|$ is at most $(\mathrm{absNorm}\,v)^{\kappa}$; (iii) the product $W_f\cdot(W_f'\cdot F_f)$ is invariant under left translation by elements of [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); (iv) for $v\notin S$ there is an additive character $\psi$ of the completion at $v$ which is trivial on $\mathcal{O}_v$, non-trivial at some $r/\varpi_v$ with $r\in\mathcal{O}_v$, and such that $W_f(\mathrm{finFactor}(\mathrm{placeEmbed}\,v\,(\mathrm{unipotent}\,x)\cdot g))=\psi(x)W_f(\mathrm{finFactor}\,g)$ for all $x$ and all $g$; (v) for $v\notin S$, $W_f\circ\mathrm{finFactor}$ is invariant under right multiplication by elements of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the pullback along `localEmbed` of the finite-adelic level-one subgroup of level the unit ideal); (vi) the same right invariance for the product $W_f'\cdot F_f$; (vii) the torus recursion: for $v\notin S$, every $g$ with trivial component at $v$, and all $m,n\in\mathbb{Z}$, the product $W_f\cdot(W_f'\cdot F_f)$ evaluated at $g\cdot\mathrm{placeEmbed}\,v\,\bigl(\mathrm{diagZ}(\varpi_v)^{\phantom{n}}\!\!{}_m\cdot \mathrm{scalarPi}(\varpi_v)^n\bigr)$ equals, when $0\le m$ and $0\le n$, the factor $(\mathrm{om}_v\,\mathrm{om}'_v)^{n}\,\mathrm{heckeRecursionSeq}(N_v,\mathrm{lam}_v,\mathrm{om}_v)(m)\,\mathrm{heckeRecursionSeq}(N_v,\mathrm{lam}'_v,\mathrm{om}'_v)(m)$ times $W_f(\mathrm{finFactor}\,g)\cdot(W_f'(\mathrm{finFactor}\,g)\cdot F_f(\mathrm{finFactor}\,g))$, and $0$ otherwise; here $N_v$ is the absolute norm of $v$ and `heckeRecursionSeq` is the sequence with values $1$, $\mathrm{lam}/N$ and $a_{m+2}=(\mathrm{lam}\,a_{m+1}-\mathrm{om}\,a_m)/N$. *Support at the bad places*: the hypothesis `_hsupp` asserts the existence of a compact set $\mathrm{Cpt}$ in `finiteAdelicGL2Subgroup ℚ` and a bound $B_0$ such that $\|W_f(g)(W_f'(g)F_f(g))\|\le B_0$ for all $g$, and such that whenever $g$ has, at every $v\notin S$, a local component of the form $n'k'$ with $n'$ in the range of the unipotent homomorphism and $k'$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), and $W_f(g)(W_f'(g)F_f(g))\neq 0$, there are a finite unipotent $n$ and an $h\in\mathrm{Cpt}$ with $\mathrm{localAt}\,v\,(ng)=\mathrm{localAt}\,v\,h$ for every $v\in S$.
--
--   Conclusion (with $\mathrm{GL}_2(\mathbb{R})$ given its Borel $\sigma$-algebra): there exists a real abscissa $\sigma_d$ such that for every $s\in\mathbb{C}$ with $\sigma_d<\operatorname{Re} s$, every Haar measure $\nu_0$ on the idele group $(\mathbb{A}_{\mathbb{Q}})^{\times}$, every Haar measure $\mu_f$ on `finiteAdelicGL2Subgroup ℚ`, every Haar measure $\mu_{N,\mathrm{arch}}$ on `realUnipotent`, every Haar measure $\mu_{N,\mathrm{fin}}$ on `finUnipotent`, and every $g\in D$, the family
--   $$\xi\longmapsto \bigl\|\,\mathrm{godementSection}\ \mathbb{Q}\ \nu_0\ 1\ 1\ (\mathrm{moduleChar}\ \mathbb{Q})\ (\mathrm{moduleChar\_pos}\ \mathbb{Q})\ \Phi\ (s-\tfrac12)\ \bigl(w\,n(\xi)\,g\bigr)\bigr\|,\qquad \xi\in\mathbb{Q},$$
--   is summable, where $w=\mathrm{adelicWeyl}\,(\mathcal{O}_{\mathbb{Q}})\,\mathbb{Q}$ is the adelic image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi)=\mathrm{unipotentGL2}$ of the image of $\xi$ in $\mathbb{A}_{\mathbb{Q}}$. Both multiplicative characters entering the Godement section are trivial, and the character used for the $\mathrm{cpow}$ twist is `moduleChar ℚ`, the positive real character given by the distributive Haar character of $\mathbb{A}_{\mathbb{Q}}$; by the definition of `godementSection`, the summand is the norm of $\bigl(\mathrm{moduleChar}(\det(w\,n(\xi)g))\bigr)^{s}$ times the Tate zeta integral with respect to $\nu_0$ of $t\mapsto \Phi\bigl(t\cdot(\text{bottom row of }w\,n(\xi)g)\bigr)$ against the trivial character at exponent $2s$. Only absolute convergence of this series is asserted; no value or analytic continuation is claimed.
--
--   This is the first side condition of the Rankin–Selberg integral over $\mathbb{Q}$: absolute convergence, in a right half-plane and uniformly over the slab domain $D$, of the Bruhat expansion $\sum_{\xi}f_{s-1/2}(w\,n(\xi)\,g)$ of the Godement section attached to the Schwartz–Bruhat function $\Phi$. It is stated under the full hypothesis package of the Rankin–Selberg data over $\mathbb{Q}$ and is used by [`LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_summable_integrable_rs22_sideConditions_of_measurable_rat), which collects the convergence and integrability conditions needed to run the Rankin–Selberg computation in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.lean

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

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open NumberField.AdelicFourier
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open AutomorphicForm
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.exists_forall_summable_norm_godementSection_bruhat_one_one_rat
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
      (∀ g ∈ D, Summable fun ξ : ℚ =>
        ‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2)
          (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ) * g)‖) := by sorry
