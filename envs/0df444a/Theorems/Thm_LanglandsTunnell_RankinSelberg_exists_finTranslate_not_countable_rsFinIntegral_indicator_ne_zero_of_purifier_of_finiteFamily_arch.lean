-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch
-- name    : LanglandsTunnell.RankinSelberg.exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/1aba0e5e-d4da-56ec-8c2d-89a5bf6300be
-- title:
--   Uncountable non-vanishing of the cut finite Rankin–Selberg factor
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ that is integral. Let $\Phi$ be a Hecke eigensystem for $\mathbb{Q}$ with complex coefficients, i.e. a level ideal $\Phi.\mathrm{level} \ne 0$ together with families $\Phi.a$, $\Phi.b$ indexed by the height-one primes of $\mathcal{O}_{\mathbb{Q}}$.
--
--   The data are organised in the following groups, all of which are hypotheses of the statement.
--
--   *Exceptional sets and Dirichlet bounds.* A finite set $S_Q$ of primes of $\mathcal{O}_{\mathbb{Q}}$ with `hSQ`: every $p$ with $\Phi.\mathrm{level} \le p$ lies in $S_Q$, and every prime $\mathfrak{P}$ of $\mathcal{O}_K$ whose trace $\mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}}$ avoids $S_Q$ is unramified (`ramificationIdx' = 1`). The hypothesis `hb` asserts $\|\Phi.b\,p\| = 1$ off $S_Q$, and `ha` asserts absolute convergence of $\sum_p \|\Phi.a\,p\| N(p)^{-\sigma}$ for every $\sigma > 1$. A finite set $S_K$ of primes of $\mathcal{O}_K$ with `hSK`: $\mathfrak{P} \in S_K$ exactly when its trace lies in $S_Q$.
--
--   *Archimedean parameter and the reference realisation.* A real archimedean parameter $P$ (either principal, given by $(u_1,a_1,u_2,a_2)$ with $a_i \in \mathbb{Z}/2$, or discrete, given by $(u_0,n)$ with $n \ge 1$); a finite $S \subseteq S_Q$; a smooth cuspidal realisation $R$ of $\Phi.\mathrm{toRawCentral}$ (the eigensystem with $b$ divided by the absolute norm) for the production pins of $\mathbb{Q}$, with $R$ continuous (`hRc`) and exceptional set contained in $S$ (`hRS`); a function $C_{\mathrm{fin}}$ on finite adeles times $\mathrm{GL}_2(\mathbb{A})$. The conditions `hP1`, `hP2` constrain the principal case ($|\mathrm{Re}(u_1-u_2)| < 1$, and $u_1-u_2 = p \in \mathbb{Z}\setminus\{0\}$ forces $a_1-a_2 \ne p+1$ in $\mathbb{Z}/2$), and `hRcen` says the central character of $R$, transported along the top-subgroup equivalence, has archimedean component at each real place given by the exponent $P.\mathrm{centralExponent}+1$ and the integer $P.\mathrm{centralSign}.\mathrm{val}$.
--
--   *The finite family of forms.* Families $\varphi_{\mathrm{par}}$, $W_r$, $k_w$ indexed by parities $\mathrm{par} : \mathrm{InfinitePlace}(\mathbb{Q}) \to \mathbb{Z}/2$, subject to: `hiso` ($\varphi_{\mathrm{par}}$ is an isotypic cusp form of level $\Phi.\mathrm{level}$ with central character $R.\mathrm{centralChar}$, Hecke eigenvalues $\Phi.a$ off $S$ and central eigenvalues $\Phi.\mathrm{toRawCentral}.b$ off $S$), `hφne` (non-vanishing), `hφKf` (each $\varphi_{\mathrm{par}}$ is fixed by right convolution with some factorizable test function), `hφarch` (archimedean weight character $\mathrm{archWeightCharAt}$ of weight $k_w(\mathrm{par},w)$ at each real place), `hkw1`, `hkw2` (the weights are determined by $P$: sums of sign shifts in the principal case, $n+1$ in the discrete case), `hφW` (the Whittaker coefficient at $1$ of $\varphi_{\mathrm{par}}$ on $\mathrm{diagOne}(a)\,g$ with $g$ in the finite adelic subgroup factorises as a product of archimedean factors $W_r$ evaluated at the real embeddings of $a$, times $C_{\mathrm{fin}}$), and `hWr1`–`hWr4` (the symmetry, support and Mellin-transform properties of the archimedean Whittaker functions $W_r$: the $\pm$-reflection rule in the principal case with $a_1 = a_2$, vanishing on the negative half-line in the discrete case, and explicit Mellin transforms of $t \mapsto (W_r(t) + (-1)^{a}W_r(-t))/t$ equal to $(2s+u_1+u_2-1)/(4\pi)$ times the archimedean $\Gamma$-factor of $P.\mathrm{twist}\,0\,a_1$, respectively to the archimedean factor of $P.\mathrm{twist}\,0\,b$, on suitable right half-planes).
--
--   *Idele class characters over $K$.* A finite set $T_q$ of primes of $\mathcal{O}_{\mathbb{Q}}$; an admissible twist $\omega$ of $K$ (idele class character, continuous, unitary) with `hωT` (off $T_q$ it is unramified and its value on the uniformizer idele equals the base-changed eigensystem coefficient $(\mathrm{formalBaseChange}\ \mathbb{Q}\ K\ \Phi).b$), `hE` ($T_q$-fibres lie in $S_K$), and `hωR`, `hωC` (archimedean components at real and complex places prescribed by $P$ through $\mathrm{archOfParamR}$, $\mathrm{archOfParamC}$). An admissible twist $\mu$ of $K$ with `hoff`: $\mu$ is not, in the stated sense, the base change of any admissible twist $\eta$ of $\mathbb{Q}$ (no $\eta$ matches $\mu$ on uniformizer ideles at all commonly unramified primes via the inertia degree). The hypothesis `hdepth` is a lower bound, for every $w \in S_K$, of the conductor exponent of the local component of $\mu$ at $w$ by four times the count of the level at $w$ plus the additive character level plus one.
--
--   *The rational twist and the conductor bookkeeping.* An admissible twist $\chi_A$ of $\mathbb{Q}$ with `hχoff` (unramified off $S_Q$), conductor exponents $k_\chi(p)$ at $p \in S_Q$ (`hkχ`), and trivial archimedean components at real places (`hχinf`). Bounds $c_0(p)$ with `hν`: at every $p \in S_Q$ and every $w$ in the fibre of $p$ in $K$, the local component of $\mu\,(\chi_A \circ \mathrm{idelicNorm})^{-1}$ has conductor exponent at most $c_0(p)$. Exponents $b_Q(p)$ with `hbQ` ($p^{b_Q(p)}$ exactly divides $\Phi.\mathrm{level}$), and `hkfloor`, the explicit numerical inequality bounding $k_\chi(p)$ from below by the displayed expression in $b_Q(p)$, $c_0(p)$, the inertia degrees, ramification indices and additive character levels over the fibre of $p$. A further admissible twist $\nu$ of $K$ with `hμν`: $\mu = \nu \cdot (\chi_A \circ \mathrm{idelicNorm})$ for the genuine base change. Families $u_R, a_R$ at real places and $u_C, k_C$ at complex places of $K$ with `hcR`, `hcC` prescribing the archimedean components of $\mu$.
--
--   *Global additive character and the cubic induction form.* A global additive character $\psi$ (principally invariant, continuous, non-trivial) with all local levels $0$ (`hlev`) and $\psi^{-1} = \psi_{\mathbb{Q}}$ (`hψQ`). A cubic induction form $F$ on $\mathrm{GL}_3$ over $\mathbb{Q}$ for the production pins built from the class-representative Siegel set with parameters $(1/2,1,1/2,2)$, the levels $\mathrm{levelOne} \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators and the adelic box, with character $\psi$ and twist $\nu$. The hypotheses on $F$ are: `hF0` ($F.\mathrm{form} \ne 0$, and at every unramified place with additive level $0$ the local Whittaker function takes value $1$ at $1$ and has spherical torus values for $\mathrm{inducedCoeff}\,K\,\nu$), continuity `hFc`, `hFw`, `hFdw`, gauge majorisation `hFg`, `hFdg` of the Whittaker and dual Whittaker functions, and `hBad`: for every finite set $T$ of primes, at every bad place in $T$ the local Whittaker function is invariant under some open subgroup and generates every non-zero subspace of its own $\mathrm{GL}_3$-cyclic span.
--
--   *Purifying data at $p$.* A finite $S' \supseteq S_Q$ with `hgood` ($\mu$ has no bad place outside $S'$); uniformizers $\varpi_p$ in the local integers with `hπ` (non-zero off $S_Q$) and `hϖ` (valuation $\exp(-1)$ off $S_Q$); local $\mathrm{GL}_3$ vectors $m_P(p)$ for $p \in S_Q$ with `hmPmem` (each lies in the $\mathrm{GL}_3$-cyclic span of $g \mapsto \chi_{A,p}(\det g)\,F.\mathrm{whittakerLoc}_p(g)$), `hmP1` ($m_P(p)(1)=1$), `hW₃admM` (admissibility: for every open subgroup, the invariant vectors of the cyclic span of $m_P(p)$ lie in the span of a finite set) and `hW₃irrM` (irreducibility of that cyclic span). An element $h_{\mu f}$ of the finite adelic $\mathrm{GL}_2$-subgroup whose underlying matrix is, by `hhμf`, the product over $p \in S' \setminus S_Q$ of the place-embedded scalar matrices $\mathrm{scalarPi}(\varpi_p)$ raised to $-\mathrm{inducedLevelAt}\,K\,\mu\,p$.
--
--   *The split of the Whittaker coefficient.* Families $W_A$ (on $\mathrm{GL}_2(\mathbb{R})$) and $W_f$ (on the finite adelic subgroup) with `hWAf`: the Whittaker coefficient at $1$ of $\varphi_{\mathrm{par}}$ against $\psi_{\mathbb{Q}}$ equals $W_A(\mathrm{par})$ at the real archimedean part times $W_f(\mathrm{par})$ at the finite factor; `hWfC` ($W_f = C_{\mathrm{fin}}(1,\cdot)$) and `hWf1` ($W_f(\mathrm{par})(1) \ne 0$). The hypothesis `hV` states, for each parity and each $p \in S_Q$, that the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$ is irreducible (every non-zero vector generates it by right translates), admissible (finitely generated invariants for each open subgroup) and smooth (each vector is right invariant under some open subgroup). Furthermore, $w_0 \in \mathrm{GL}_2(\mathbb{Q})$ is the antidiagonal involution $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀`), and $W_{fd}$ is the dual finite vector defined by `hWfd` as the idele norm of the determinant times $W_f$ evaluated at the finite factor of $w_0 \cdot {}^{t}g^{-1}$.
--
--   *The chosen place and purifier.* A parity $\mathrm{par}$, a prime $p \in S_Q$, a vector $w_{2b}$ in the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$, and purifier data: $n_P \in \mathbb{N}$, coefficients $c_P : \mathrm{Fin}\,n_P \to \mathbb{C}$ and local elements $x_P : \mathrm{Fin}\,n_P \to \mathrm{GL}_2(\mathbb{Q}_p)$ such that, by `hnd`, the purified finite vector
--   $$g_f \longmapsto \sum_j c_P(j)\,\|\det(g_f\,\iota_p x_P(j))\|^{-1/2}\,W_f(\mathrm{par})\big(\mathrm{finFactor}(g_f\,\iota_p x_P(j))\big)$$
--   is non-zero at some point of the finite adelic subgroup, where $\iota_p$ denotes the place embedding at $p$ and $\|\cdot\|$ the idele norm.
--
--   The conclusion is: for every Haar measure $\mu_{fH}$ on the finite adelic $\mathrm{GL}_2$-subgroup of $\mathbb{Q}$ and every Haar measure $\mu_{NF}$ on its finite unipotent subgroup, there exist
--
--   (i) an element $h_{3f} \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ whose archimedean component is $1$, whose component at $p$ is $1$, and whose component at every prime $v \notin S_Q$ is $1$; and
--
--   (ii) a natural number $m$, coefficients $d : \mathrm{Fin}\,m \to \mathbb{C}$ and elements $k : \mathrm{Fin}\,m \to \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ such that each $k(j)$ has archimedean component $1$ and component $1$ at every prime $v \ne p$,
--
--   for which, for every real $\sigma'$, the set of $s \in \mathbb{C}$ with $\mathrm{Re}\,s > \sigma'$ at which the finite Rankin–Selberg integral $\mathrm{rsFinIntegral}\,\mu_{fH}\,\mu_{NF}\,s$ of the following two vectors is non-zero is not countable.
--
--   The first vector is the indicator, on the set of $g$ in the finite adelic subgroup such that at every prime $v \notin S_Q$ the local component $\mathrm{localAt}_v(g)$ factors as $n\,k$ with $n$ in the image of the unipotent homomorphism over $\mathbb{Q}_v$ and $k$ in $\mathrm{localLevelOne}_v(\top)$, of the purified finite vector of `hnd` evaluated at $\mathrm{finFactor}(g)$.
--
--   The second vector is the indicator of the same big-cell set, applied to the function sending $g$ to the product of
--   $$\sum_j d(j)\,\chi_{A,p}\!\big(\det(y \cdot k(j)_p)\big)\,F.\mathrm{whittakerLoc}_p\big(y \cdot k(j)_p\big), \qquad y = \iota_{\mathrm{GL}}\big(\mathrm{localAt}_p(g)\big),$$
--   with the finite product over all primes $v$ of the factors equal to $1$ at $v = p$ and equal to
--   $$\chi_{A,v}\!\big(\det(\iota(g)_v \cdot (h_{3f})_v)\big)\,F.\mathrm{whittakerLoc}_v\big(\iota(g)_v \cdot (h_{3f})_v\big)$$
--   at $v \ne p$, both evaluated at $\mathrm{finFactor}(g)$; here $\iota$ is the embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$ in the upper left corner, $\iota_{\mathrm{GL}}$ its local version, and $\chi_{A,v}$ the local component of $\chi_A$ at $v$.
--
--   No holomorphy in $s$ and no Euler factorisation are asserted: the conclusion is pointwise non-vanishing on an uncountable subset of each right half-plane.
--
--   This is the finite half of the non-vanishing input to the converse-theorem step of the Langlands–Tunnell argument: the finite Rankin–Selberg integral of a purified member of the arithmetic family against a $\mathrm{GL}_3$ Whittaker vector built from the cubic induction form, cut off $S_Q$ to the big cell $N \cdot K_1$, is shown to be non-zero at uncountably many points of every right half-plane. It is used by the statement producing a combination of pure translates with non-vanishing global Rankin–Selberg integral, where the archimedean factor supplies the complementary half and the identity theorem then yields non-vanishing of the completed integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch
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
    (w₂b : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂b : w₂b ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par))

    (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
    (hnd : ∃ gf : finiteAdelicGL2Subgroup ℚ,
      (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
              Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) gf ≠ 0) :

    ∀ (μfH : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μfH.IsHaarMeasure]
      (μNF : MeasureTheory.Measure RSCarrier.finUnipotent) [μNF.IsHaarMeasure],
    ∃ (h₃f : AdelicGL 3 (𝓞 ℚ) ℚ), archComponent3 (𝓞 ℚ) ℚ h₃f = 1 ∧ componentAt3 (𝓞 ℚ) ℚ p h₃f = 1 ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v h₃f = 1) ∧
    ∃ (m : ℕ) (d : Fin m → ℂ) (k : Fin m → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ j, archComponent3 (𝓞 ℚ) ℚ (k j) = 1 ∧
        ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → componentAt3 (𝓞 ℚ) ℚ v (k j) = 1) ∧
    ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧
        RSCarrier.rsFinIntegral μfH μNF s

          ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
              Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))

          ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun y : LocalGL3 p => ∑ j, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
            (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              (if v = p then (1 : ℂ) else
                ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
                    (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) *
                  F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)))) ≠ 0} := by sorry
