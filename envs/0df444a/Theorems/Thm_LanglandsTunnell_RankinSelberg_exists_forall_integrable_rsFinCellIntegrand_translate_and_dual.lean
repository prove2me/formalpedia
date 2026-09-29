-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_rsFinCellIntegrand_translate_and_dual
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_rsFinCellIntegrand_translate_and_dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/bb616345-3deb-5d90-92fa-9ef181c72b85
-- title:
--   Half-plane integrability of primal and dual finite cell integrands
-- statement:
--   Throughout, $K$ is a number field equipped with an algebra structure over $\mathcal O_{\mathbb Q}$ making $\mathcal O_K$ integral over $\mathcal O_{\mathbb Q}$, and `_hdeg` records that $K$ has degree $3$ over $\mathbb Q$. **The $\mathrm{GL}_2$ side.** $\Phi$ is a Hecke eigensystem for $\mathbb Q$ with values in $\mathbb C$, that is, a nonzero ideal $\Phi.\mathrm{level}$ of $\mathcal O_{\mathbb Q}$ together with two families $\Phi.a$, $\Phi.b$ of complex numbers indexed by the height-one primes of $\mathcal O_{\mathbb Q}$. A finite set $SQ$ of such primes is given, and `hSQ` has two clauses: every prime $p$ with $\Phi.\mathrm{level}\subseteq p$ lies in $SQ$, and every prime $\mathfrak P$ of $\mathcal O_K$ whose prime below in $\mathcal O_{\mathbb Q}$ lies outside $SQ$ has ramification index $1$. Further, `hb` requires $\lVert\Phi.b\,p\rVert=1$ for $p\notin SQ$, and `ha` requires, for every real $\sigma>1$, summability of $p\mapsto\lVert\Phi.a\,p\rVert\,\mathrm N(p)^{-\sigma}$ over all height-one primes. A finite set $SK$ of primes of $\mathcal O_K$ is given with `hSK`: $\mathfrak P\in SK$ if and only if the prime under $\mathfrak P$ lies in $SQ$. A further finite set $S\subseteq SQ$ is given.
--
--   $R$ is a smooth cuspidal realisation, relative to the carrier pins `productionPinsGeneral ℚ`, of the eigensystem $\Phi.\mathrm{toRawCentral}$ (same level and same $a$, with $b$ replaced by $v\mapsto \mathrm N(v)^{-1}\Phi.b\,v$): a function on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ that is nonzero somewhere, a central character $R.\mathrm{centralChar}$, smooth cuspidality at those pins, right invariance under the level subgroup, a finite exceptional set, and the Hecke and central eigenvalue identities off that set; `hRc` asserts that $R.\mathrm{toFun}$ is continuous, and `hRS` that $R.\mathrm{exceptionalSet}\subseteq S$. $Cfin$ is a function of two arguments, a finite adele and an element of $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$, with complex values. A family $\varphi_{\mathrm{par}}$ of complex functions on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ is indexed by the parities $\mathrm{par}\colon \mathrm{InfinitePlace}\,\mathbb Q\to\mathbb Z/2$. For each parity, `hiso` asserts `IsIsotypicCuspFormAt` for the pins `productionPinsGeneral ℚ`, the central character $R.\mathrm{centralChar}$, the level $\Phi.\mathrm{level}$, the set $S$ and the eigensystem $\Phi$: smooth cuspidality at those pins, continuity, right invariance under the level subgroup of the pins, the coset Hecke eigenvalue $\Phi.a\,v$ at every $v\notin S$, and the central relation $\varphi(z(\det \mathrm{gen}\,v)g)=\mathrm N(v)^{-1}\Phi.b\,v\cdot\varphi(g)$ for $v\notin S$. In addition `hφne` requires $\varphi_{\mathrm{par}}\neq0$, and `hφKf` requires each $\varphi_{\mathrm{par}}$ to be fixed by right convolution against some factorisable test function (archimedean factor given by a smooth compactly supported function of the matrix entries, finite factor a finite test factor). **Characters.** $\mu$ is a character of the idele group of $K$ with values in $\mathbb C^\times$, and `hμ` states that $\mu$ is admissible: trivial on $K^\times$, continuous, and unitary. $\psi$ is an additive character of $\mathbb A_{\mathbb Q}$ with `hψ`: invariant under the principal adeles, continuous and nontrivial; `hlev` states that each local component $\mathrm{psiLoc}\,\psi\,v$ has additive level $0$, and `hψQ` that $\psi^{-1}$ is the standard character $\psi_{\mathbb Q}$. **The $\mathrm{GL}_3$ side.** $F$ is a cubic induction form for $K$, $\psi$ and $\mu$, relative to the pins `productionPinsOf` formed from the class-representative Siegel set `classRepSiegelSet ℚ (1/2) 1 (1/2) 2`, the level subgroups $N\mapsto \mathrm{levelOne}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $v\mapsto \mathrm{heckeGen}\,v$ and the adelic box. Such a form carries data $F.\mathrm{form}$, $F.\mathrm{whittaker}$, local Whittaker functions $F.\mathrm{whittakerLoc}\,v$ on $\mathrm{GL}_3$ of the completion at $v$, an archimedean Whittaker function, a central character and $F.\mathrm{dualWhittaker}$, subject to a long list of axioms (summarised here): automorphy under $\mathrm{GL}_3(\mathbb Q)$, the central character law, ideles-class triviality of that character, cuspidality along the two maximal parabolics, the identification of $F.\mathrm{whittaker}$ with the $\psi$-Whittaker integral of $F.\mathrm{form}$ and the corresponding transformation law, the mirabolic Fourier expansion, the local $\psi_v$-Whittaker laws, factorisation of the global Whittaker function into the archimedean factor times the finite local factors over any finite set containing the bad places, induced sphericity and level invariance away from bad and ramified places, local multiplicity one, moderate growth, $K$-finiteness, and further growth and moment conditions. The hypothesis `hF0` has two parts: $F.\mathrm{form}\neq0$, and for every finite place $v$ that is not ramified in $K$ and at which $\mathrm{psiLoc}\,\psi\,v$ has level $0$, the normalisation $F.\mathrm{whittakerLoc}\,v\,1=1$ together with `HasSphericalTorusValuesAt` for the induced coefficients $\mathrm{inducedCoeff}\,K\,\mu$, i.e. the explicit formulae for the values of $F.\mathrm{whittakerLoc}\,v$ at the torus points $\mathrm{iotaTorusLocal}\,v\,n$ and at the two-row points in terms of spherical torus values of the three induced Satake parameters. Continuity of $F.\mathrm{form}$, $F.\mathrm{whittaker}$ and $F.\mathrm{dualWhittaker}$ is assumed (`hFc`, `hFw`, `hFdw`), as is gauge majorisation `IsGaugeMajorised3` for $F.\mathrm{whittaker}$ and for $F.\mathrm{dualWhittaker}$ (`hFg`, `hFdg`): there are $t$, a finite set of primes and a bound $B$ such that for every $N$ some constant $C$ makes the function vanish outside the root level determined by $B$ and satisfy there the decay bound $C/(\mathrm{rootSizeProd}^t(1+\mathrm{archRootSum})^N)$. The bad-place hypothesis `hBad` states, for every finite set $T$ of primes: for each $v\in T$ that is a bad place for $(K,\mu)$ there is an open subgroup $U_v$ of $\mathrm{GL}_3$ of the completion at $v$ under which $F.\mathrm{whittakerLoc}\,v$ is right invariant; and for each such $v$, every nonzero $W$ in the cyclic subspace generated by $F.\mathrm{whittakerLoc}\,v$ under right translation satisfies $F.\mathrm{whittakerLoc}\,v\in\mathrm{gl3CyclicSubspace}\,W$. **Places, uniformisers and the central translate.** A finite set $S'$ with $SQ\subseteq S'$ is given such that no $p\notin S'$ is a bad place for $(K,\mu)$ (`hgood`). A family $\varpi$ picks an element of the valuation ring at each prime $p$, with nonzero image in the completion (`hπ`) and valuation $\exp(-1)$ (`hϖ`) for $p\notin SQ$. The element $h_\mu$ of `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection) is required by `hhμf` to have underlying adelic matrix the product, over the list of primes in $S'\setminus SQ$, of the place-$p$ embeddings of the scalar matrix $\varpi_p$ raised to the power $-\mathrm{inducedLevelAt}\,K\,\mu\,p$, where this exponent is $\sum_{\mathfrak P\mid p} f(\mathfrak P/p)\cdot$ (conductor exponent of the local component of $\mu$ at $\mathfrak P$). **Whittaker factors.** Functions $W_A\colon \mathrm{par}\mapsto(\mathrm{GL}_2(\mathbb R)\to\mathbb C)$ and $W_f\colon\mathrm{par}\mapsto(\mathrm{finiteAdelicGL2Subgroup}\,\mathbb Q\to\mathbb C)$ are given with `hWAf`: for every parity and every $g$, the $\psi_{\mathbb Q}$-Whittaker coefficient of $\varphi_{\mathrm{par}}$ at $\alpha=1$ and $g$, taken with respect to the pins above, equals $W_A(\mathrm{par})(\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{par})(\mathrm{finFactor}\,g)$; `hWfC` states $W_f(\mathrm{par})(g)=Cfin\,1\,g$; `hWf1` states $W_f(\mathrm{par})(1)\neq0$. Finally $w_0\in\mathrm{GL}_2(\mathbb Q)$ has matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and the dual finite factor $W_f^{\vee}$ is determined by `hWfd`: $W_f^{\vee}(\mathrm{par})(g_f)=\lVert\det g_f\rVert\cdot W_f(\mathrm{par})\bigl(\mathrm{finFactor}(w_0\cdot{}^{t}g_f^{-1})\bigr)$, with $\lVert\cdot\rVert$ the idele norm. **Measures and the translate.** $\mu_f$ is a Haar measure on `finiteAdelicGL2Subgroup ℚ` and $\mu_{N,\mathrm{fin}}$ a Haar measure on the finite unipotent subgroup [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43). The element $k\in\mathrm{GL}_3(\mathbb A_{\mathbb Q})$ satisfies `_hk`: archimedean component $1$ and component $1$ at every finite place outside $SQ$. A parity $\mathrm{par}$ is fixed. **Conclusion.** There exists a real $\sigma$ such that for every complex $s'$ with $\sigma<\mathrm{Re}\,s'$ both of the following functions on `finiteAdelicGL2Subgroup ℚ` are integrable with respect to the measure $\mu_f$ weighted by the quotient density [`HaarQuotient.density RSCarrier.finUnipotent μNFin`](def/HaarQuotient.html#L25). Let $\mathcal C$ denote the big cell, the set of $g$ in `finiteAdelicGL2Subgroup ℚ` such that for every prime $p\notin SQ$ the local component $\mathrm{localAt}\,p\,g$ factors as $n\cdot k$ with $n$ in the image of the unipotent homomorphism $\mathrm{unipotentGL2Hom}$ over the completion at $p$ and $k\in\mathrm{localLevelOne}\,p\,\top$ (the preimage under the place-$p$ embedding of the finite level-one subgroup for the unit ideal). First conjunct: the function
--   $$g\longmapsto \mathbf 1_{\mathcal C}(g)\,W_f(\mathrm{par})(\mathrm{finFactor}\,g)\cdot\mathbf 1_{\mathcal C}(g)\Bigl(\prod^{\mathrm f}_{v} F.\mathrm{whittakerLoc}\,v\bigl(\text{component at }v\text{ of }\iota(\mathrm{finFactor}\,g)\cdot k\bigr)\Bigr)\cdot\lVert\det g\rVert^{\,s'-1/2},$$
--   where $\iota$ is the embedding of $\mathrm{GL}_2$ into $\mathrm{GL}_3$, the product is the finite product over all height-one primes $v$, and the two indicator factors are those of the functions displayed. Second conjunct: the function
--   $$g\longmapsto \mathbf 1_{\mathcal C}(g)\,W_f^{\vee}(\mathrm{par})(\mathrm{finFactor}\,g\cdot h_\mu)\cdot\mathbf 1_{\mathcal C}(g)\Bigl(\prod^{\mathrm f}_{v}\widetilde{F.\mathrm{whittakerLoc}\,v}\bigl(\text{component at }v\text{ of }\iota(\mathrm{finFactor}\,g\cdot h_\mu)\cdot{}^{t}k^{-1}\bigr)\Bigr)\cdot\lVert\det g\rVert^{\,s'-1/2},$$
--   where $\widetilde W(h)=W(w_3\cdot{}^{t}h^{-1})$ with $w_3$ the long Weyl element of $\mathrm{GL}_3$, and ${}^{t}k^{-1}=\mathrm{transposeInv3}\,k$. The abscissa $\sigma$ is produced for the fixed translate $k$ and the fixed parity; no uniformity in $k$ or in the parity is asserted.
--
--   This is the absolute-convergence statement for the finite (non-archimedean) part of the $\mathrm{GL}_2\times\mathrm{GL}_3$ Rankin–Selberg integral attached to a cubic induction form and a cuspidal Hecke eigensystem on $\mathrm{GL}_2/\mathbb Q$, in the form needed to integrate over the big cell against the quotient density of the finite unipotent subgroup, for one $\mathrm{GL}_3$-translate $k$ and one parity at a time. It feeds the twisted and split versions of the same integrability statement, from which the functional equation and the Euler product of the Rankin–Selberg integral are obtained in the converse-theorem step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_rsFinCellIntegrand_translate_and_dual.lean

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

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_rsFinCellIntegrand_translate_and_dual
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : (∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ) ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hSK : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (Cfin : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hRS : R.exceptionalSet ⊆ S)
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (hφKf : ∀ par, ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ (φv par) α = φv par)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)

    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ μ)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))

    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (hμf : finiteAdelicGL2Subgroup ℚ)
    (hhμf : (hμf : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((S' \ SQ).toList.map (fun p => if hp : p ∉ SQ then
          UnramifiedWhittaker.placeEmbed ℚ p
            ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
              (hπ p hp)) ^ (-(inducedLevelAt K μ p : ℤ)))
        else 1)).prod)

    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (hWfC : ∀ par (g : finiteAdelicGL2Subgroup ℚ), Wf par g = Cfin 1 (g : AdelicGL2 (𝓞 ℚ) ℚ))

    (hWf1 : ∀ par, Wf par 1 ≠ 0)

    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ par (gf : finiteAdelicGL2Subgroup ℚ), Wfd par gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf par (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : MeasureTheory.Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure]

    (k : AdelicGL 3 (𝓞 ℚ) ℚ) (_hk : archComponent3 (𝓞 ℚ) ℚ k = 1 ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v k = 1)
    (par : InfinitePlace ℚ → ZMod 2) :
    ∃ σ : ℝ, ∀ s' : ℂ, σ < s'.re →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wf par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))) g *
            {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v, F.whittakerLoc v
              (componentAt3 (𝓞 ℚ) ℚ v
                (iota (𝓞 ℚ) ℚ ((RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) : finiteAdelicGL2Subgroup ℚ) :
                  AdelicGL2 (𝓞 ℚ) ℚ) * k))) g *
            ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) ∧
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wfd par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)) g *
            {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v, dualWhittakerFn3 (F.whittakerLoc v)
              (componentAt3 (𝓞 ℚ) ℚ v
                (iota (𝓞 ℚ) ℚ ((RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf : finiteAdelicGL2Subgroup ℚ) :
                  AdelicGL2 (𝓞 ℚ) ℚ) * transposeInv3 k))) g *
            ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by sorry
