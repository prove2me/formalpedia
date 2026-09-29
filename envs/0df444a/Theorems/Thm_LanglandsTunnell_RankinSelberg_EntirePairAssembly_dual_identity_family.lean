-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family
-- name    : LanglandsTunnell.RankinSelberg.EntirePairAssembly.dual_identity_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/75dc7084-a55b-5109-adeb-63ace0fde7d1
-- title:
--   Dual-side family identity in the GL₂timesGL₃ entire-pair assembly
-- statement:
--   Fix a number field $K$ whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, a Hecke eigensystem $\Phi$ over $\mathbb{Q}$ with complex coefficients (a level ideal together with Satake data $p \mapsto \Phi.a\,p$, $p\mapsto \Phi.b\,p$), finite sets $SQ$ of primes of $\mathcal{O}_{\mathbb{Q}}$ and $SK$ of primes of $\mathcal{O}_K$, a real archimedean parameter $P$, two characters $\omega,\mu:(\mathbb{A}_K)^\times\to\mathbb{C}^\times$, and archimedean twisting data $uR, aR$ at the real places and $uC, kC$ at the complex places of $K$. The hypothesis `_hunr` says that every prime $p\notin SQ$ satisfies $\neg\,\mathrm{IsRamifiedIn}\;K\;p$, i.e. no prime $\mathfrak{P}$ of $K$ above $p$ has ramification index different from $1$. Fixed further are: a measurable set $Dm\subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, a constant $c\neq 0$, an additive character $\psi$ of $\mathbb{A}_{\mathbb{Q}}$ with $\psi^{-1}$ equal to the standard character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615), Haar measures $\mu f$ on the finite adelic subgroup $\ker(\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q},\infty}))$ and $\mu N\mathrm{Fin}$ on the unipotent subgroup of that group, a family $\varpi$ of elements of the local valuation rings with `hπ` (nonzero image in $\mathbb{Q}_p$ for $p\notin SQ$) and `hϖ` (valuation $\exp(-1)$ for $p\notin SQ$, so $\varpi_p$ is a uniformiser), a natural number $n$, functions $\varphi_i:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ and coefficients $\mathrm{coef}_i$ for $i\in\mathrm{Fin}\,n$, a real abscissa $\sigma_b$, and functions $\Theta_i, Wd_i:\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$.
--
--   Write $c_\mu$ for the function on primes of $K$ sending $\mathfrak{P}$ to $\mu$ of the idele which is a uniformiser at $\mathfrak{P}$ and $1$ elsewhere when $\mu$ is unramified at $\mathfrak{P}$ (that is, $\mathrm{localChar}\,\mu\,\mathfrak{P}$ is trivial on the units of the valuation ring) and to $0$ otherwise. Write $D$ for the $L$-datum `rsDatum ℚ SQ Φ.a Φ.b` $c_\mu$ with gamma multisets $\Gamma_{\mathbb{R}}=$ `twistedGammaR K (archOfParamR K P) uR aR`, $\Gamma_{\mathbb{C}}=$ `twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC`, and dual multisets obtained by replacing $P$ at every place by its dual parameter and negating $uR$, $uC$, $kC$; thus $D$ is indexed by the primes $p\notin SQ$, has norms $N(p)$, Euler polynomial `rsEulerPoly` in $\Phi.a\,p$, $\Phi.b\,p$ and the induced symmetric functions $e_1,e_2,e_3$ of $c_\mu$ over the fibre of $p$, dual polynomial the same expression in $\Phi.a\,p/\Phi.b\,p$, $(\Phi.b\,p)^{-1}$ and the $e_j$ of $c_\mu^{-1}$, abscissa $1$, centre $1/2$ and degree $6$. Write $E(s)$ for the finite correction factor $\prod_{w\in SK} \varepsilon_w(\mathrm{localChar}(\omega\mu)\,w)\,\varepsilon_w(\mathrm{localChar}\,\mu\,w)\,\bigl(N(w)^{1/2-s}\bigr)^{-(\mathrm{pinnedExp}(\omega\mu,w)+\mathrm{pinnedExp}(\mu,w))}$, with $\varepsilon_w$ the standard local root number `stdRootNumberAt`, and write $\varepsilon_{\mathrm{pin}}$ for `pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK` with the archimedean data $(\mathrm{archOfParamR}\,K\,P,\ \mathrm{archOfParamC}\,K\,P, uR,aR,uC,kC)$, and $N_\mu$ for `finiteConductor K μ SK`.
--
--   After fixing the Borel $\sigma$-algebra on $\mathrm{GL}_2(\mathbb{R})$, the assertion is universally quantified over the following further data and hypotheses.
--
--   Measure data and splittings: a Haar measure $\mu N\mathrm{Arch}$ on the real unipotent subgroup; `_hsplit`, that the pushforward of the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ under $g\mapsto(\mathrm{ratArchGL2}\,g,\ \mathrm{finFactor}\,g)$ is the product of [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) with $\mu f$; and `_hNsplit`, the corresponding splitting of the unipotent Haar measure into the pushforwards of $\mu N\mathrm{Arch}$ and $\mu N\mathrm{Fin}$.
--
--   Analytic hypotheses on the datum: `_hwf`, that $D$ is well formed (norms at least $2$, Euler and dual polynomials with constant term $1$ and degree at most $6$, all gamma shifts bounded by the abscissa); `_hLhold`, that $D.\mathrm{LFunDual}$ is holomorphic on $\{\mathrm{Re}\,s>1\}$; `_hEd`, that $s\mapsto \varepsilon_{\mathrm{pin}}\cdot N_\mu^{\,s-1/2}\cdot E(s)$ is entire; and `_hconvd`, that the datum `rsDatum ℚ SQ` with Satake data $p\mapsto \Phi.a\,p/\Phi.b\,p$, $p\mapsto(\Phi.b\,p)^{-1}$, coefficient function $c_\mu^{-1}$ and the two gamma pairs interchanged converges in the sense of `LDatum.Converges`.
--
--   The dual vector: functions $\varphi^\vee_i$ with `_hφd`: $\varphi^\vee_i(g)=\varphi_i({}^t g^{-1})\,\lVert\det g\rVert$, the idele norm of the determinant being `detNorm`.
--
--   The translating element: $h_\mu$ in the finite adelic subgroup together with `_hQT`, that for every function $f$ on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ invariant under left multiplication by the adelic unipotent subgroup, right translation by $h_\mu$ leaves both the integral over the unipotent quotient (with respect to `unipotentQuotientMeasure`, evaluated on `Quotient.out` representatives) and integrability unchanged; `_hPF`, that the idele norm of $\det h_\mu$ equals $N_\mu$; and `_hNpos`, that $N_\mu>0$.
--
--   Whittaker factorisations: functions $W^\vee_{\infty,i}$ on $\mathrm{GL}_2(\mathbb{R})$ and $W^\vee_{f,i}$ on the finite adelic subgroup with `_hWAdf`: the $\psi$-Whittaker coefficient at $\alpha=1$ of $\varphi^\vee_i$, formed with the carrier pins `productionPinsOf ℚ (classRepSiegelSet ℚ (1/2) 1 (1/2) 2)` with level subgroups $N\mapsto \mathrm{levelOne}\sqcap$ (finite adelic subgroup), Hecke generators `heckeGen` and box `adelicBox ℚ` — that is, the integral $\int_{\mathbb{A}_{\mathbb{Q}}} \varphi^\vee_i(u(x)g)\,\psi(-x)$ against the additive Haar measure conditioned on `adelicBox ℚ` — factors as $W^\vee_{\infty,i}(\mathrm{ratArchGL2}\,g)\cdot W^\vee_{f,i}(\mathrm{finFactor}\,g)$; and similarly functions $F^\vee_{\infty,i}$, $F^\vee_{f,i}$ with `_hFAdf`: $Wd_i(\iota\,g)=F^\vee_{\infty,i}(\mathrm{ratArchGL2}\,g)\cdot F^\vee_{f,i}(\mathrm{finFactor}\,g)$, where $\iota$ is the upper-left block embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$.
--
--   Local relations for the translated finite Whittaker factors: `_hHLd` asserts, for each $i$ and with $g\mapsto W^\vee_{f,i}(g\,h_\mu)$ read through `finFactor`, four clauses at each prime $p\notin SQ$: equivariance $W^\vee(u(x)g)=\psi_p(x)W^\vee(g)$ for $x\in\mathbb{Q}_p$ under the local unipotent embedding; right invariance under the local level-one subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at level $\top$; the Hecke relation that the sum over residues $r$ modulo $p$ of the values at $g\cdot\mathrm{repSome}(\varpi_p,r)$ plus the value at $g\cdot\mathrm{repInf}(\varpi_p)$ equals $(\Phi.a\,p/\Phi.b\,p)$ times the value at $g$; and the central relation that translation by $\mathrm{scalarPi}(\varpi_p)$ multiplies the value by $(\Phi.b\,p)^{-1}/N(p)$.
--
--   Dual Satake recursions: a family $hH^\vee_p(k)$ with `_hHdrec` giving $hH^\vee_p(0)=1$, $hH^\vee_p(1)=e_1$, $hH^\vee_p(2)=e_1^2-e_2$ and $hH^\vee_p(k+3)=e_1\,hH^\vee_p(k+2)-e_2\,hH^\vee_p(k+1)+e_3\,hH^\vee_p(k)$, where $e_j=\mathrm{inducedE}_j$ of $c_\mu^{-1}$ at $p$; a family $uH^\vee_p(k_1,k_2)$ with `_uHdrec`: $uH^\vee_p(k,0)=hH^\vee_p(k)$ and $uH^\vee_p(k_1,k_2+1)=hH^\vee_p(k_1)hH^\vee_p(k_2+1)-hH^\vee_p(k_1+1)hH^\vee_p(k_2)$; and an extension $uZ^\vee_p$ to integer pairs with `_uZdrec`: it vanishes when $m_2<0$ or $m_1<m_2$ and agrees with $uH^\vee_p$ on naturals $k_2\le k_1$.
--
--   Torus table for the translated finite cubic factors: `_hTTd` asserts, for each $i$ and with $g\mapsto F^\vee_{f,i}(g\,h_\mu)$, right invariance under the local level-one subgroup at each $p\notin SQ$, and, for $g$ with trivial component at $p$ and all $m_1,m_2\in\mathbb{Z}$, that translating $g$ by $\mathrm{diagZ}(\varpi_p)^{m_1-m_2}\cdot\mathrm{scalarPi}(\varpi_p)^{m_2}$ multiplies the value by $N(p)^{-m_1}\,uZ^\vee_p(m_1,m_2)$.
--
--   Unfolding of the dual global integrals: functions $f^\vee_i(s',g)$ with `_hfd`: $f^\vee_i(s',g)$ is the $\psi$-Whittaker coefficient of $\varphi^\vee_i$ at $\alpha=1$ evaluated at $g$, times $Wd_i(\iota\,g)$, times $\lVert\det g\rVert^{s'-1/2}$; `_hJ3df`, that for each $i$ there is $\sigma_0$ such that for $\mathrm{Re}\,s'>\sigma_0$ the global integral $\int_{Dm}\varphi^\vee_i(g)\,\Theta_i({}^t(\iota g)^{-1})\,\lVert\det g\rVert^{s'-1/2}$ equals $c$ times $\int f^\vee_i(s',\cdot)$ over the unipotent quotient; `_hfdm`, measurability of each $f^\vee_i(s',\cdot)$; `_hfdN`, its invariance under left multiplication by the adelic unipotent subgroup; and `_hintd7`, that for each $i$ there is $\sigma_7$ beyond which the unfolded integrand is integrable on the quotient.
--
--   The finite cells and the family archimedean identity: functions $\kappa^\vee_i$ with `_hJ5ad`, that for $\mathrm{Re}\,s'>\sigma_b$ the finite Rankin–Selberg integral [`RSCarrier.rsFinIntegral`](def/LanglandsTunnell_RSCarrier.html#L46) $\mu f\,\mu N\mathrm{Fin}$ at $s'$ of the two translated factors, each restricted by the indicator of the set of $g$ whose component at every $p\notin SQ$ factors as a local unipotent element times an element of the local level-one subgroup at level $\top$, equals $\kappa^\vee_i(s')$; and `_hJ5bd`, that for $\mathrm{Re}\,s>\sigma_b$
--   $$\sum_i \mathrm{coef}_i\,\Bigl(\mathrm{rsArchIntegral}\bigl(\mathrm{archMeasure},\mu N\mathrm{Arch},s-\tfrac12,W^\vee_{\infty,i},F^\vee_{\infty,i}\bigr)\cdot\kappa^\vee_i\bigl(s-\tfrac12\bigr)\Bigr)=\varepsilon_{\mathrm{pin}}\cdot N_\mu^{1/2}\cdot E(s)\cdot D.\mathrm{archFactorDual}(s).$$
--
--   Finally, `_hdiff`, that $s\mapsto c^{-1}\sum_i \mathrm{coef}_i\,\mathrm{rsGlobalIntegral}\,Dm\,(s-\tfrac12)\,\varphi_i\,\Theta_i$ is entire, and `_hfe`, that for all $s$ this function equals $c^{-1}\sum_i \mathrm{coef}_i\,\mathrm{rsGlobalIntegral}\,Dm\,((1-s)+\tfrac12)\,\bigl(g\mapsto\varphi_i({}^tg^{-1})\bigr)\,\mathrm{dualForm}(\Theta_i)$.
--
--   Under all of the above, the conclusion is a single identity: for every $s\in\mathbb{C}$ with $\mathrm{Re}\,s>1$,
--   $$c^{-1}\sum_i \mathrm{coef}_i\,\mathrm{rsGlobalIntegral}\,Dm\,\bigl(s+\tfrac12\bigr)\,\bigl(g\mapsto\varphi_i({}^tg^{-1})\bigr)\,\mathrm{dualForm}(\Theta_i) =\varepsilon_{\mathrm{pin}}\cdot N_\mu^{\,s-1/2}\cdot E(s)\cdot D.\mathrm{archFactorDual}(s)\cdot D.\mathrm{LFunDual}(s),$$
--   where the left-hand integral is $\int_{Dm}\varphi_i({}^tg^{-1})\,\Theta_i\bigl({}^t(\iota g)^{-1}\bigr)\,\lVert\det g\rVert^{s}$ against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, $D.\mathrm{archFactorDual}(s)$ is the product of $\Gamma_{\mathbb{R}}(s+\nu)$ over the dual real gamma multiset and $\Gamma_{\mathbb{C}}(s+\nu)$ over the dual complex one, and $D.\mathrm{LFunDual}(s)=\prod_{p\notin SQ}\bigl(\mathrm{dual}_p(N(p)^{-s})\bigr)^{-1}$.
--
--   This is the dual-side member identity of the $\mathrm{GL}_2\times\mathrm{GL}_3$ Rankin–Selberg entire-pair assembly, in the form where the cubic data $(\Theta_i, Wd_i)$ and the finite cells $\kappa^\vee_i$ vary with the index $i$ and the archimedean comparison is a single identity for the whole family: it identifies the analytically continued dual integral of the family with the expected product of root number, conductor power, archimedean factor and dual Euler product. It is used in the construction of the entire, bounded-on-strips completion of the Rankin–Selberg $L$-function attached to the base change of $\Phi$ twisted by $\mu$, which supplies the analytic input to the converse theorem in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_EntirePairAssembly_dual_identity_family.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.Converse

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.EntirePairAssembly.dual_identity_family
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (P : RealArchParam)
    (ω μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (_hunr : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ¬ IsRamifiedIn K p)
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)] [hIfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (Dm : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (c : ℂ) (hc0 : c ≠ 0)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (μf : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : MeasureTheory.Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure]
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    {n : ℕ} (φ : Fin n → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (coef : Fin n → ℂ) (σb : ℝ)

    (Θ Wd : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μNArch : MeasureTheory.Measure RSCarrier.realUnipotent) [μNArch.IsHaarMeasure]
      (_hsplit : MeasureTheory.Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (ratArchGL2 g, RSCarrier.finFactor g))
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = RSCarrier.archMeasure.prod μf)
      (_hNsplit : MeasureTheory.Measure.map
        (fun n : adelicUnipotent ℚ => (ratArchGL2 (n : AdelicGL2 (𝓞 ℚ) ℚ), RSCarrier.finFactor n))
        (unipotentHaar ℚ) =
        (MeasureTheory.Measure.map Subtype.val μNArch).prod (MeasureTheory.Measure.map Subtype.val μNFin))
      (_hwf : (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).WellFormed)
      (_hLhold : DifferentiableOn ℂ (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFunDual
        {s : ℂ | (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).abscissa < s.re})
      (_hEd : Differentiable ℂ (fun s : ℂ => (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P)
        uR aR uC kC) *
        (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2) *
        (fun t : ℂ => ∏ w : ↥SK,
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
        (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
        (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) s))
      (_hconvd : (rsDatum ℚ SQ (fun p => Φ.a p / Φ.b p) (fun p => (Φ.b p)⁻¹)
        (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual)
        (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)).Converges)

      (φd : Fin n → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (_hφd : ∀ i g, φd i g = φ i (transposeInvN (Fin 2) g) * ((detNorm g : ℝ) : ℂ))

      (hμf : finiteAdelicGL2Subgroup ℚ)
      (_hQT : ∀ f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
        (∀ (u : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f ((u : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f g) →
        (∫ q, f (Quotient.out q * (hμf : AdelicGL2 (𝓞 ℚ) ℚ)) ∂(unipotentQuotientMeasure ℚ) =
            ∫ q, f (Quotient.out q) ∂(unipotentQuotientMeasure ℚ)) ∧
          (MeasureTheory.Integrable (fun q : UnipotentQuotient ℚ => f (Quotient.out q * (hμf : AdelicGL2 (𝓞 ℚ) ℚ)))
              (unipotentQuotientMeasure ℚ) ↔
            MeasureTheory.Integrable (fun q : UnipotentQuotient ℚ => f (Quotient.out q)) (unipotentQuotientMeasure ℚ)))
      (_hPF : TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (hμf : AdelicGL2 (𝓞 ℚ) ℚ)) = finiteConductor K μ SK)
      (_hNpos : 0 < finiteConductor K μ SK)

      (WAd : Fin n → GL (Fin 2) ℝ → ℂ) (Wfd : Fin n → finiteAdelicGL2Subgroup ℚ → ℂ)
      (_hWAdf : ∀ (i : Fin n) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ (φd i) 1 g = WAd i (ratArchGL2 g) * Wfd i (RSCarrier.finFactor g))

      (_hHLd : ∀ i : Fin n,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.unipotent x) * g)) =
            psiLoc ψ p x * (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) =
                (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repSome
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
            (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repInf
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            (Φ.a p / Φ.b p) * (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.scalarPi
            (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            ((Φ.b p)⁻¹ / (Ideal.absNorm p.asIdeal : ℂ)) * (fun g => Wfd i (g * hμf)) (RSCarrier.finFactor g)))
      (FAd : Fin n → GL (Fin 2) ℝ → ℂ) (Ffd : Fin n → finiteAdelicGL2Subgroup ℚ → ℂ)
      (_hFAdf : ∀ (i : Fin n) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wd i (iota (𝓞 ℚ) ℚ g) = FAd i (ratArchGL2 g) * Ffd i (RSCarrier.finFactor g))

      (hHd : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℂ)
      (_hHdrec : (∀ p, hHd p 0 = 1) ∧ (∀ p, hHd p 1 = inducedE1 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p) ∧
        (∀ p, hHd p 2 = inducedE1 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p ^ 2 - inducedE2 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p) ∧
        (∀ p (n : ℕ), hHd p (n + 3) = inducedE1 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p * hHd p (n + 2) - inducedE2 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p * hHd p (n + 1) +
          inducedE3 ℚ (fun 𝔓 => ((fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) 𝔓)⁻¹) p * hHd p n))
      (uHd : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℕ → ℂ)
      (_uHdrec : (∀ p k, uHd p k 0 = hHd p k) ∧
        (∀ p k₁ k₂, uHd p k₁ (k₂ + 1) = hHd p k₁ * hHd p (k₂ + 1) - hHd p (k₁ + 1) * hHd p k₂))
      (uZd : HeightOneSpectrum (𝓞 ℚ) → ℤ → ℤ → ℂ)
      (_uZdrec : (∀ p (m₁ m₂ : ℤ), (m₂ < 0 ∨ m₁ < m₂) → uZd p m₁ m₂ = 0) ∧
        (∀ p (k₁ k₂ : ℕ), k₂ ≤ k₁ → uZd p k₁ k₂ = uHd p k₁ k₂))
      (_hTTd : ∀ i : Fin n,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) =
                (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m₁ m₂ : ℤ),
          localAt ℚ p g = 1 →
            (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p
                (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
                    (hπ p hp) (m₁ - m₂) *
                  UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
                    (hπ p hp) ^ m₂))) =
              (fun g => Ffd i (g * hμf)) (RSCarrier.finFactor g) * ((Ideal.absNorm p.asIdeal : ℂ)⁻¹ ^ m₁ * uZd p m₁ m₂)))

      (fd : Fin n → ℂ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (_hfd : ∀ i s' g, fd i s' g =
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ (φd i) 1 g * Wd i (iota (𝓞 ℚ) ℚ g) *
          ((detNorm g : ℝ) : ℂ) ^ (s' - 1 / 2))
      (_hJ3df : ∀ i, ∃ σ0 : ℝ, ∀ s' : ℂ, σ0 < s'.re →
        rsGlobalIntegral Dm s' (φd i) (dualForm (Θ i)) = c * ∫ q, fd i s' (Quotient.out q) ∂(unipotentQuotientMeasure ℚ))

      (_hfdm : ∀ (i : Fin n) (s' : ℂ), Measurable (fd i s'))
      (_hfdN : ∀ (i : Fin n) (s' : ℂ) (u : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        fd i s' ((u : AdelicGL2 (𝓞 ℚ) ℚ) * g) = fd i s' g)
      (_hintd7 : ∀ i : Fin n, ∃ σ7 : ℝ, ∀ s' : ℂ, σ7 < s'.re →
        MeasureTheory.Integrable (fun q : UnipotentQuotient ℚ => fd i s' (Quotient.out q)) (unipotentQuotientMeasure ℚ))

      (κd : Fin n → ℂ → ℂ)
      (_hJ5ad : ∀ i (s' : ℂ), σb < s'.re →
        RSCarrier.rsFinIntegral μf μNFin s'
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wfd i (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)))
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Ffd i (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf))) = κd i s')
      (_hJ5bd : ∀ s : ℂ, σb < s.re →
        ∑ i, coef i *
          (RSCarrier.rsArchIntegral RSCarrier.archMeasure μNArch (s - 1 / 2) (WAd i) (FAd i) * κd i (s - 1 / 2)) =
        (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P)
          uR aR uC kC) * (((finiteConductor K μ SK) : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * (fun t : ℂ => ∏ w : ↥SK,
          LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
          LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
          (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
          (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) s * (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).archFactorDual s)
      (_hdiff : Differentiable ℂ
        (fun s : ℂ => c⁻¹ * ∑ i, coef i * rsGlobalIntegral Dm (s - 1 / 2) (φ i) (Θ i)))
      (_hfe : ∀ s : ℂ, (c⁻¹ * ∑ i, coef i * rsGlobalIntegral Dm (s - 1 / 2) (φ i) (Θ i)) =
        c⁻¹ * ∑ i, coef i * rsGlobalIntegral Dm ((1 - s) + 1 / 2) (fun g => φ i (transposeInvN (Fin 2) g))
          (dualForm (Θ i))),
    ∀ s : ℂ, 1 < s.re →
      c⁻¹ * ∑ i, coef i *
          rsGlobalIntegral Dm (s + 1 / 2) (fun g => φ i (transposeInvN (Fin 2) g)) (dualForm (Θ i)) =
        (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P)
          uR aR uC kC) *
          (((finiteConductor K μ SK) : ℝ) : ℂ) ^ (s - 1 / 2) *
          (fun t : ℂ => ∏ w : ↥SK,
          LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
          LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
          (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
          (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) s *
          (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).archFactorDual s *
          (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K (archOfParamR K P) uR aR)
          (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
          (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFunDual s := by sorry
