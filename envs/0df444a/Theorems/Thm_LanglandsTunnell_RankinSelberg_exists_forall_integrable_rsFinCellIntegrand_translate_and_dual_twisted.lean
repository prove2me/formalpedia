-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_rsFinCellIntegrand_translate_and_dual_twisted
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_rsFinCellIntegrand_translate_and_dual_twisted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/34b32830-fae6-5b83-a4fb-613adfefc7c4
-- title:
--   Integrability of the twisted Rankin–Selberg finite-cell integrands
-- statement:
--   The setting is a Rankin–Selberg pairing of a $\mathrm{GL}_2$-eigenform over $\mathbb{Q}$ with a $\mathrm{GL}_3$ form obtained by cubic induction from a cubic field, the inducing character being twisted by an idele class character of $\mathbb{Q}$ composed with the determinant.
--
--   **Data.** A number field $K$ equipped with an algebra structure $\mathcal O_{\mathbb Q}\to\mathcal O_K$ that is integral, with `_hdeg` asserting $[K:\mathbb Q]=3$; a Hecke eigensystem $\Phi$ over $\mathbb Q$ with values in $\mathbb C$ (a non-zero level ideal $\Phi.\mathrm{level}$ together with families $\Phi.a$, $\Phi.b$ indexed by the finite places); finite sets $S_{\mathbb Q}$, $S$, $S'$ of finite places of $\mathbb Q$ and a finite set $S_K$ of primes of $K$; a smooth cuspidal realisation $R$ of $\Phi.\mathrm{toRawCentral}$ (the eigensystem with central eigenvalues rescaled by $(\mathrm{cNorm}\,v)^{-1}$) for the carrier pins `productionPinsGeneral ℚ`; an auxiliary function $C_{\mathrm{fin}}$ on pairs (finite adele, adelic $\mathrm{GL}_2$ element); a family $\varphi_{\mathrm{par}}$ of functions on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ indexed by parity vectors $\mathrm{par}\colon \mathrm{InfinitePlace}\,\mathbb Q\to\mathbb Z/2$; idele class characters $\mu,\nu$ of $K$ and $\chi_A$ of $\mathbb Q$; an additive character $\psi$ of $\mathbb A_{\mathbb Q}$; a cubic induction form $F$ for $(K,\psi,\nu)$ relative to the pins `productionPinsOf ℚ (classRepSiegelSet ℚ (1/2) 1 (1/2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)` — a structure recording an automorphic, cuspidal, moderately growing function `F.form` on $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$ with central character, its global, local and archimedean $\psi$-Whittaker functions `F.whittaker`, `F.whittakerLoc v`, `F.whittakerArch`, its dual Whittaker function `F.dualWhittaker`, together with the Whittaker expansion, the factorisation of `F.whittaker` into archimedean and local factors outside any finite set containing the bad places of $(K,\nu)$, sphericality and level invariance of the local factors, local multiplicity one, $K$-finiteness and further analytic clauses; a choice $\varpi_p$ of an element of the valuation ring at each finite place $p$; an element $h_\mu$ of the finite adelic subgroup `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection); families $W_A$, $W_f$, $W_f^\vee$ of archimedean and finite Whittaker factors indexed by parity; an element $w_0$ of $\mathrm{GL}_2(\mathbb Q)$; Haar measures $\mu_f$ on `finiteAdelicGL2Subgroup ℚ` and $\mu_{N,\mathrm{fin}}$ on [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), the unipotent subgroup of the finite adelic subgroup; an element $k$ of $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$; and a parity vector $\mathrm{par}$.
--
--   **Hypotheses, by group.** On the eigensystem and the exceptional sets: `hSQ` asks that every $p$ with $\Phi.\mathrm{level}\subseteq p$ lie in $S_{\mathbb Q}$ and that every prime $\mathfrak P$ of $K$ lying over a place outside $S_{\mathbb Q}$ have ramification index $1$; `hb` that $\lVert\Phi.b\,p\rVert=1$ off $S_{\mathbb Q}$; `ha` that $\sum_p\lVert\Phi.a\,p\rVert\,\mathrm{N}(p)^{-\sigma}$ converges for every real $\sigma>1$; `hSK` that $\mathfrak P\in S_K$ if and only if its contraction to $\mathcal O_{\mathbb Q}$ lies in $S_{\mathbb Q}$; `hS` that $S\subseteq S_{\mathbb Q}$; `hRS` that $R.\mathrm{exceptionalSet}\subseteq S$; and `hRc` the continuity of $R.\mathrm{toFun}$.
--
--   On the isotypic vectors: `hiso` asks that each $\varphi_{\mathrm{par}}$ be an isotypic cusp form at `productionPinsGeneral ℚ` with central character $R.\mathrm{centralChar}$, level $\Phi.\mathrm{level}$ and exceptional set $S$ for $\Phi$ — that is, a continuous smooth cuspidal automorphic function, right invariant under the level subgroup, a Hecke eigenfunction with eigenvalue $\Phi.a\,v$ outside $S$ and transforming under the central scalar $\det$ of the Hecke generator by $\Phi.\mathrm{toRawCentral}.b\,v$; `hφne` that each $\varphi_{\mathrm{par}}$ be non-zero; `hφKf` that each $\varphi_{\mathrm{par}}$ be fixed by right convolution with some factorizable test function.
--
--   On the characters: `hμ`, `hνadm`, `hχA` assert that $\mu$, $\nu$, $\chi_A$ are admissible twists, i.e. continuous unitary idele class characters; `hχoff` that $\chi_A$ be unramified at every $v\notin S_{\mathbb Q}$; `hχinf` that at every real place of $\mathbb Q$ the archimedean component of $\chi_A$ satisfy `IsArchCompAt ℚ χA v 0 0`, i.e. be identically $1$; and `hμν` the twisting relation $\mu=\nu\cdot(\chi_A\circ\text{idelic norm of the base change }\mathbb Q\to K)$. On the additive character: `hψ` that $\psi$ be a global additive character (principal invariant, continuous, non-trivial), `hlev` that every local component $\mathrm{psiLoc}\,\psi\,v$ have level $0$, and `hψQ` that $\psi^{-1}$ be the standard character $\psi_{\mathbb Q}$.
--
--   On the cubic induction form: `hF0` asks that `F.form` be non-zero and that at every place $v$ unramified in $K$ whose local additive character has level $0$ one has $F.\mathrm{whittakerLoc}\,v\,(1)=1$ and that $F.\mathrm{whittakerLoc}\,v$ have the spherical torus values attached to the coefficients $\mathrm{inducedCoeff}\,K\,\nu$; `hFc`, `hFw`, `hFdw` the continuity of `F.form`, `F.whittaker` and `F.dualWhittaker`; `hFg`, `hFdg` gauge majorisation (`IsGaugeMajorised3`) of `F.whittaker` and `F.dualWhittaker`; and `hBad`, for every finite set $T$ of finite places, the two clauses that at each $v\in T$ which is a bad place for $(K,\nu)$ the function $F.\mathrm{whittakerLoc}\,v$ be right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb Q_v)$, and that $F.\mathrm{whittakerLoc}\,v$ lie in the cyclic subspace generated by every non-zero member of its own cyclic subspace.
--
--   On the level-shifting translate: `hSS'` asks $S_{\mathbb Q}\subseteq S'$; `hgood` that no $p\notin S'$ be a bad place for $(K,\mu)$; `hπ` and `hϖ` that for $p\notin S_{\mathbb Q}$ the element $\varpi_p$ be a non-zero element of valuation $\exp(-1)$, hence a uniformiser; and `hhμf` that the image of $h_\mu$ in $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ be the product, over the places $p$ in $S'\setminus S_{\mathbb Q}$ listed by `(S' \\ SQ).toList`, of the images under [`UnramifiedWhittaker.placeEmbed ℚ p`](def/UnramifiedWhittaker_HeckeRecursion.html#L47) of the scalar matrices $\mathrm{scalarPi}(\varpi_p)^{-\,\mathrm{inducedLevelAt}\,K\,\mu\,p}$ (the factor being $1$ at places of $S_{\mathbb Q}$).
--
--   On the Whittaker factorisation: `hWAf` asks that for every parity and every $g$ the Whittaker coefficient of $\varphi_{\mathrm{par}}$ at $\alpha=1$ with respect to $\psi_{\mathbb Q}$ and the pins above factor as $W_A(\mathrm{par})(\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{par})(\mathrm{finFactor}\,g)$; `hWfC` that $W_f(\mathrm{par})(g)=C_{\mathrm{fin}}\,1\,g$; `hWf1` that $W_f(\mathrm{par})(1)\neq 0$; `hw₀` that $w_0$ be the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$; and `hWfd` the definition of the dual finite factor, $W_f^\vee(\mathrm{par})(g_f)=\lVert\det g_f\rVert\cdot W_f(\mathrm{par})\bigl(\mathrm{finFactor}(w_0\cdot{}^t g_f^{-1})\bigr)$, where $\lVert\cdot\rVert$ is the idele norm. Finally `_hk` asks that the archimedean component of $k$ be $1$ and that its component at every $v\notin S_{\mathbb Q}$ be $1$.
--
--   **Conclusion.** There exists a real $\sigma$ such that for every complex $s'$ with $\sigma<\operatorname{Re} s'$ both of the following functions on `finiteAdelicGL2Subgroup ℚ` are integrable with respect to the Haar measure $\mu_f$ weighted by the density [`HaarQuotient.density RSCarrier.finUnipotent μNFin`](def/HaarQuotient.html#L25). Write $\mathcal C$ for the big cell, the set of $g$ in the finite adelic subgroup such that for every $p\notin S_{\mathbb Q}$ the component $\mathrm{localAt}\,p\,g$ factors as $n\cdot k_p$ with $n$ in the range of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33) over $\mathbb Q_p$ and $k_p\in\mathrm{AdelicDock.localLevelOne}\,(\mathcal O_{\mathbb Q})\,\mathbb Q\,p\,\top$, and write $\chi_{A,v}$ for the local component of $\chi_A$ at $v$.
--
--   First conjunct: the function
--   $$g\mapsto \mathbf 1_{\mathcal C}(g)\,W_f(\mathrm{par})(\mathrm{finFactor}\,g)\;\cdot\;\mathbf 1_{\mathcal C}(g)\prod_v{}^{\!\mathrm f}\;\chi_{A,v}\bigl(\det\bigr)\cdot F.\mathrm{whittakerLoc}\,v\Bigl(\bigl(\iota(\mathrm{finFactor}\,g)\cdot k\bigr)_v\Bigr)\;\cdot\;\lVert\det g\rVert^{\,s'-1/2},$$
--   the two indicator factors being those of the same set $\mathcal C$, the product being the finitary product `∏ᶠ` over the finite places $v$ of the twisted local Whittaker function evaluated at the component at $v$ of $\iota(\mathrm{finFactor}\,g)\cdot k$, where $\iota$ is the embedding of adelic $\mathrm{GL}_2$ into adelic $\mathrm{GL}_3$, and the last factor the complex power of the idele norm of $\det g$.
--
--   Second conjunct: the function
--   $$g\mapsto \mathbf 1_{\mathcal C}(g)\,W_f^\vee(\mathrm{par})(\mathrm{finFactor}\,g\cdot h_\mu)\;\cdot\;\mathbf 1_{\mathcal C}(g)\prod_v{}^{\!\mathrm f}\;\mathrm{dualWhittakerFn3}\bigl(\chi_{A,v}(\det)\cdot F.\mathrm{whittakerLoc}\,v\bigr)\Bigl(\bigl(\iota(\mathrm{finFactor}\,g\cdot h_\mu)\cdot{}^tk^{-1}\bigr)_v\Bigr)\;\cdot\;\lVert\det g\rVert^{\,s'-1/2},$$
--   where $\mathrm{dualWhittakerFn3}\,W\,(x)=W(\mathrm{longWeyl3}\cdot{}^tx^{-1})$ and ${}^tk^{-1}$ is `transposeInv3 k`.
--
--   The abscissa $\sigma$ is allowed to depend on all the data, in particular on the translate $k$ and on the parity $\mathrm{par}$.
--
--   This is the absolute-convergence side condition for the finite-place cell integrals in the $\mathrm{GL}_2\times\mathrm{GL}_3$ Rankin–Selberg method, in the form needed when the inducing character $\nu$ of the cubic field is twisted by $\chi_A\circ\det$: it guarantees that, in a right half-plane, both the primal and the dual finite integrands of the big cell are integrable on the finite adelic $\mathrm{GL}_2$ quotient. It is used by the statement assembling the finite family of $\mathrm{GL}_3$-translated cell integrals into a constant value and its functional-equation counterpart with root-number monomial, on the converse-theorem route to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_rsFinCellIntegrand_translate_and_dual_twisted.lean

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
import Definitions.Def_M4aHerbrand_GenuineDescent

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_rsFinCellIntegrand_translate_and_dual_twisted
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

    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (hμν : μ = ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)

    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K ν v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K ν v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
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
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v,
              (fun g : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc v g)
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
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v, dualWhittakerFn3
              (fun g : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc v g)
              (componentAt3 (𝓞 ℚ) ℚ v
                (iota (𝓞 ℚ) ℚ ((RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf : finiteAdelicGL2Subgroup ℚ) :
                  AdelicGL2 (𝓞 ℚ) ℚ) * transposeInv3 k))) g *
            ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by sorry
