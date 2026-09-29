-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/0d65e019-d2c9-5bc6-b2a9-d7d230ae2c15
-- title:
--   Local integrability of the Rankin–Selberg integrand at p
-- statement:
--   **Ambient data.** $K$ is a number field whose ring of integers carries an $\mathcal O_{\mathbb Q}$-algebra structure making $\mathcal O_K$ integral over $\mathcal O_{\mathbb Q}$, and `_hdeg` records $\operatorname{finrank}_{\mathbb Q} K = 3$. $\Phi$ is a Hecke eigensystem over $\mathbb Q$ with complex values, i.e. a nonzero level ideal `Φ.level` of $\mathcal O_{\mathbb Q}$ together with two families $\Phi.a,\Phi.b$ indexed by the finite places of $\mathbb Q$.
--
--   **Places, size and growth of the eigensystem.** $SQ$ is a finite set of finite places of $\mathbb Q$ and `hSQ` has two clauses: every $p$ with $\Phi.\mathrm{level}\le p$ lies in $SQ$, and every prime $\mathfrak P$ of $K$ whose trace to $\mathbb Q$ avoids $SQ$ has ramification index $1$. `hb` requires $\lVert\Phi.b\,p\rVert=1$ for $p\notin SQ$, and `ha` requires, for each real $\sigma>1$, summability of $p\mapsto \lVert\Phi.a\,p\rVert\,N(p)^{-\sigma}$. The finite set $SK$ of primes of $K$ is characterised by `hSK`: $\mathfrak P\in SK$ exactly when $\mathfrak P$ lies over a place in $SQ$.
--
--   **Archimedean parameter.** $P$ is a real archimedean parameter, either principal, given by $(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb C$ and $a_i\in\mathbb Z/2$, or discrete, given by $(u_0,n)$ with $n\ge 1$. In the principal case `hP1` demands $|\operatorname{Re}(u_1-u_2)|<1$ and `hP2` demands that if $u_1-u_2$ is a nonzero integer $m$ then $a_1-a_2\neq m+1$ in $\mathbb Z/2$ (both clauses are stated for an arbitrary real place).
--
--   **The $GL_2$ realisation.** $S\subseteq SQ$ is finite, $R$ is a smooth cuspidal realisation of the central renormalisation `Φ.toRawCentral` (same level and $a$, with $b$ divided by the absolute norm) for the production carrier pins of $\mathbb Q$ — Borel structure and adelic Haar measure on $GL_2(\mathbb A_{\mathbb Q})$, the Siegel-set fundamental domain `classRepSiegelSet ℚ (1/2) 1 (1/2) 2`, full central subgroup, level subgroups $N\mapsto \mathrm{levelOne}(N)\cap$ the finite adelic subgroup, Hecke generators `heckeGen`, and the adelic box as conditioning set; `hRc` asserts continuity of $R$, `hRS` that its exceptional set is contained in $S$, and `hRcen` that the central character of $R$, read as a character of the full idele group, has archimedean component at each real place with exponent $P.\mathrm{centralExponent}+1$ and sign $P.\mathrm{centralSign}$ in the sense of `IsArchCompAt`. $C_{\mathrm{fin}}$ is an auxiliary function of a finite adele and an adelic matrix.
--
--   **The family of isotypic cusp forms and its Whittaker data.** For each parity vector $\mathrm{par}\colon \mathrm{InfinitePlace}\,\mathbb Q\to\mathbb Z/2$ there are a function $\varphi_{\mathrm{par}}$ on $GL_2(\mathbb A_{\mathbb Q})$, archimedean Whittaker functions $W_{\mathrm r}(\mathrm{par},w,\cdot)$ on $\mathbb C$ and weights $k_w(\mathrm{par},w)\in\mathbb Z$. The hypotheses require: `hiso`, each $\varphi_{\mathrm{par}}$ is an isotypic cusp form of level $\Phi.\mathrm{level}$ with central character $R.\mathrm{centralChar}$, continuous, invariant under the level subgroup, a Hecke coset eigenfunction with eigenvalue $\Phi.a\,v$ and central eigenvalue $(\Phi.\mathrm{toRawCentral}).b\,v$ for $v\notin S$; `hφne`, $\varphi_{\mathrm{par}}\neq0$; `hφKf`, each $\varphi_{\mathrm{par}}$ is reproduced by right convolution against some factorisable test function (a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor); `hφarch`, $\varphi_{\mathrm{par}}$ transforms at each real place $w$ by the character `archWeightCharAt hw (kw par w)`; `hkw1` and `hkw2`, the weights are $\mathrm{signShift}(a_1+\mathrm{par}\,w)+\mathrm{signShift}(a_2+\mathrm{par}\,w)$ in the principal case and $n+1$ in the discrete case; `hφW`, the first Whittaker coefficient of $\varphi_{\mathrm{par}}$ at $\mathrm{diag}(a,1)g$, for $g$ in the finite adelic subgroup, factors as $\prod_w W_{\mathrm r}(\mathrm{par},w,a_w)$ times $C_{\mathrm{fin}}$ of the finite part of $a$ at $g$. Four further clauses constrain $W_{\mathrm r}$: `hWr1`, the parity relation $W_{\mathrm r}(\mathrm{par},w,-t)=(-1)^{a_1}W_{\mathrm r}(\mathrm{par},w,t)$ when $P$ is principal with $a_1=a_2=\mathrm{par}\,w$; `hWr2`, vanishing on the negative reals in the discrete case; `hWr3` and `hWr4`, Mellin convergence in a right half plane of $t\mapsto (W_{\mathrm r}(\mathrm{par},w,t)+(-1)^{b}W_{\mathrm r}(\mathrm{par},w,-t))/t$ together with the values $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$ and $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$ of its Mellin transform, in the two cases $b=a_1$ with $\mathrm{par}\,w=a_1+1$, respectively $b\in\{\mathrm{par}\,w,\ \mathrm{par}\,w+P.\mathrm{centralSign}\}$.
--
--   **Idele class characters of $K$.** $Tq$ is a finite set of finite places of $\mathbb Q$; $\omega$ is an admissible twist of $K$ (a continuous unitary idele class character), unramified at every $\mathfrak P$ lying over a place outside $Tq$ with $\omega$ of a uniformiser there equal to $(\mathrm{formalBaseChange}\ \mathbb Q\ K\ \Phi).b\,\mathfrak P=(\Phi.b\,p)^{f(\mathfrak P/p)}$ (`hωT`), and `hE` says primes over $Tq$ lie in $SK$; `hωR` and `hωC` prescribe the archimedean components of $\omega$ at real and complex places by `archOfParamR` and `archOfParamC` applied to $P$. $\mu$ is a further admissible twist of $K$ subject to: `hoff`, $\mu$ is not matched by any admissible twist $\eta$ of $\mathbb Q$ in the sense that no such $\eta$ satisfies $\mu(\varpi_{\mathfrak P})=\eta(\varpi_{p})^{f(\mathfrak P/p)}$ at all $\mathfrak P$ where both are unramified; `hdepth`, for every $w\in SK$ the conductor exponent of the local component of $\mu$ at $w$ is at least $4$ times the multiplicity of $w$ in the extension of $\Phi.\mathrm{level}$ plus the level of the standard local additive character at $w$ plus $1$. $\chi_A$ is an admissible twist of $\mathbb Q$, unramified outside $SQ$ (`hχoff`), with conductor exponents $k_\chi(p)$ at $p\in SQ$ (`hkχ`) and trivial archimedean data at real places (`hχinf`). The function $c_0$ bounds, by `hν`, the conductor exponents at all primes $w$ of $K$ over $p\in SQ$ of the local components of $\mu\cdot(\chi_A\circ\text{idelic norm})^{-1}$; $b_Q(p)$ is by `hbQ` the exact exponent of $p$ in $\Phi.\mathrm{level}$; and `hkfloor` imposes, for each $p\in SQ$, an explicit linear lower bound for $k_\chi(p)$ built from $b_Q(p)$, $c_0(p)$, the constant $52$ and a sum over the primes of $K$ above $p$ of their inertia degrees, ramification indices and the levels of the standard local additive characters (the inequality is stated in full in the Lean). Finally $\nu$ is an admissible twist of $K$ with $\mu=\nu\cdot(\chi_A\circ\text{idelic norm of }\mathrm{genuineBaseChange})$ (`hμν`), and the families $u_{\mathbb R},a_{\mathbb R},u_{\mathbb C},k_{\mathbb C}$ record, by `hcR` and `hcC`, the archimedean components of $\mu$ at the real and complex places of $K$.
--
--   **The additive character and the cubic induction form.** $\psi$ is a global additive character of $\mathbb A_{\mathbb Q}$ (trivial on $\mathbb Q$, continuous, nontrivial) all of whose local levels vanish (`hlev`) and with $\psi^{-1}$ the standard character `psiQ` (`hψQ`). $F$ is a cubic induction form for $K$ over the production pins written out explicitly, for $\psi$ and $\nu$: a $GL_3$ automorphic function together with its global, local and archimedean Whittaker functions, a central character and a dual Whittaker function, satisfying the structure's axioms. The hypotheses on $F$ are: `hF0`, $F.\mathrm{form}\neq0$ and, at each place $v$ unramified in $K$ with local additive level $0$, $F.\mathrm{whittakerLoc}\,v\,1=1$ and $F.\mathrm{whittakerLoc}\,v$ has the spherical torus values attached to `inducedCoeff K ν`; `hFc`, `hFw`, `hFdw`, continuity of the form, of the Whittaker function and of the dual Whittaker function; `hFg`, `hFdg`, gauge majorisation `IsGaugeMajorised3` of the latter two; and `hBad`, for every finite set $T$ of finite places, at each bad place $v\in T$ for $(K,\nu)$ the local Whittaker function is invariant under right translation by some open subgroup of $GL_3(\mathbb Q_v)$, and every nonzero element of its cyclic subspace generates it back.
--
--   **Local normalisations.** $S'\supseteq SQ$ is finite and `hgood` says places outside $S'$ are not bad for $(K,\mu)$. The family $\varpi$ picks a local integer at each $p$, nonzero (`hπ`) and of valuation $\exp(-1)$, i.e. a uniformiser, for $p\notin SQ$ (`hϖ`). For $p\in SQ$, $m_P(p)$ is a local $GL_3$ function lying in the cyclic subspace generated by $g\mapsto \chi_{A,p}(\det g)\,F.\mathrm{whittakerLoc}\,p\,g$ (`hmPmem`), normalised by $m_P(p)(1)=1$ (`hmP1`), with `hW₃admM` the admissibility statement that for each open subgroup $U_v$ a finite set spans the $U_v$-invariant vectors of that cyclic subspace, and `hW₃irrM` the irreducibility statement that every nonzero member of the subspace generates $m_P(p)$ back. The element $h_{\mu f}$ of the finite adelic subgroup is prescribed by `hhμf` as the product over $p\in S'\setminus SQ$ of the local embeddings of the scalar matrices $\varpi_p\cdot I_2$ raised to $-\mathrm{inducedLevelAt}\,K\,\mu\,p$. The functions $W_A$ and $W_f$ split the first Whittaker coefficient of $\varphi_{\mathrm{par}}$ as $W_A(\mathrm{par})$ of the archimedean component times $W_f(\mathrm{par})$ of the finite component (`hWAf`), with $W_f(\mathrm{par})=C_{\mathrm{fin}}(1,\cdot)$ (`hWfC`) and $W_f(\mathrm{par})(1)\neq0$ (`hWf1`). The hypothesis `hV` states, for every parity vector and every $p\in SQ$, the three standard properties of the local Whittaker space `localSpaceAt` of $\varphi_{\mathrm{par}}$ at $p$: irreducibility (any nonzero member generates the space under right translates), admissibility (finitely many spanning vectors for the invariants of each open subgroup) and smoothness (each member is invariant under some open subgroup). The matrix $w_0\in GL_2(\mathbb Q)$ is the antidiagonal involution $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀`), and $W_{fd}$ is defined by `hWfd` as the idele norm of the determinant times $W_f(\mathrm{par})$ evaluated at the finite component of $w_0\cdot{}^{t}g^{-1}$.
--
--   **Local input and conclusion.** A parity vector $\mathrm{par}$ and a place $p\in SQ$ are fixed. The function $w$ on $GL_2(\mathbb Q_p)$ lies in the complex span of the right translates $g\mapsto w_0'(gh)$ of elements $w_0'$ of the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$ (for the standard character `psiQ`), and $W_3$ on $GL_3(\mathbb Q_p)$ lies in the cyclic subspace generated by $g\mapsto \chi_{A,p}(\det g)\,F.\mathrm{whittakerLoc}\,p\,g$.
--
--   With $GL_2(\mathbb Q_p)$ given its Borel $\sigma$-algebra, the assertion is: for every Haar measure $\mu_2$ on $GL_2(\mathbb Q_p)$ and every Haar measure $\mu_{N_2}$ on the image of `unipotentGL2Hom`, i.e. on the subgroup of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, there exists $\sigma_2\in\mathbb R$ such that for every $s\in\mathbb C$ with $\operatorname{Re}s>\sigma_2$ the function
--   $$g\ \longmapsto\ W_3(\iota(g))\,w(g)\,\lvert\det g\rvert_p^{\,s-1/2}$$
--   is integrable against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_{N_2}$, that is against the measure on $GL_2(\mathbb Q_p)$ representing the quotient $N\backslash GL_2(\mathbb Q_p)$. Here $\iota$ is the embedding $g\mapsto\begin{pmatrix}g&0\\0&1\end{pmatrix}$ of $GL_2$ into $GL_3$ and $\lvert\cdot\rvert_p$ is `modulus`, the Haar scaling factor of the local field. Only integrability is asserted; no value or analytic continuation of the integral is claimed, and the conclusion involves the data of the last group, the global hypotheses serving to fix the ambient situation.
--
--   This is the local integrability input for the $GL_3\times GL_2$ Rankin–Selberg integrals over $N_p\backslash GL_2(\mathbb Q_p)$ attached to the cubic induction form and the isotypic $GL_2$ family, in the half plane $\operatorname{Re}s\gg0$. It is used in the step establishing that a finite translate of the corresponding finite-adelic Rankin–Selberg integral is not identically zero, on the way to the converse-theorem construction in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch.lean

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
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory LanglandsTunnell.TateLocal in

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch
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
    (P : RealArchParam)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (Cfin : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hRS : R.exceptionalSet ⊆ S)
    (hP1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (hP2 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (hRcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ))
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Wr : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℂ → ℂ)
    (kw : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℤ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (hφKf : ∀ par, ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ (φv par) α = φv par)
    (hφarch : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (kw par w)) (φv par))
    (hkw1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w))
    (hkw2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hφW : ∀ par, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (φv par) 1 (diagOne a * g)
          = (∏ w : InfinitePlace ℚ, Wr par w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
              * Cfin (a : AdeleRing (𝓞 ℚ) ℚ).2 g)
    (hWr1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par w ∨ b = par w + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (Tq : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓)
    (hE : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ Tq → 𝔓 ∈ SK)
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent
        ((archOfParamR K P w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hdepth : ∀ w : ↥SK,
      4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1))
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (kχ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hkχ : ∀ p ∈ SQ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar χA p) (kχ p))
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0)
    (c₀ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hν : ∀ p ∈ SQ, ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ p ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w
        (NumberField.TateGlobal.localChar
          (μ * (χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)⁻¹) w) c)
    (bQ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hbQ : ∀ p ∈ SQ, p.asIdeal ^ bQ p ∣ Φ.level ∧ ¬ p.asIdeal ^ (bQ p + 1) ∣ Φ.level)
    (hkfloor : ∀ p ∈ SQ,
      6 * ((bQ p : ℤ) + 3 * (2 * ((∑ᶠ w ∈ primeFibre ℚ K p,
              ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                    (2 * ((52 : ℤ) + 3 * (c₀ p : ℤ)) +
                      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                  (c₀ p : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
            ((52 : ℤ) + 3 * (c₀ p : ℤ)))) + 3) + 7 ≤ (kχ p : ℤ))
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (hμν : μ = ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
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
    (mP : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)
    (hmPmem : ∀ p : ↥SQ, mP p ∈ gl3CyclicSubspace
      (fun g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) g))
    (hmP1 : ∀ p : ↥SQ, mP p 1 = 1)
    (hW₃admM : ∀ p : ↥SQ, ∀ Uv : Subgroup (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))), IsOpen (Uv : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))) →
      ∃ B : Finset (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ), ∀ W ∈ gl3CyclicSubspace (mP p),
        (∀ k ∈ Uv, ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)))
    (hW₃irrM : ∀ p : ↥SQ, ∀ W ∈ gl3CyclicSubspace (mP p), W ≠ 0 → mP p ∈ gl3CyclicSubspace W)
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
    (hV : ∀ par, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ →
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)))
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ par (gf : finiteAdelicGL2Subgroup ℚ), Wfd par gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf par (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (par : InfinitePlace ℚ → ZMod 2) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)

    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw : w ∈ Submodule.span ℂ {f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ |
      ∃ w₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
        ∃ h : GL (Fin 2) (p.adicCompletion ℚ), f = fun g => w₀ (g * h)})

    (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ ∈ gl3CyclicSubspace
      (fun g : LocalGL3 p => ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (W₃ (iotaGL g) * w g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := by sorry
