-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
-- name    : LanglandsTunnell.RankinSelberg.exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/98d78f99-7ea9-5283-b5dc-e4f0b345507c
-- title:
--   A p-adic purifier with pure-tensor Whittaker coefficient
-- statement:
--   Throughout, $K$ is a number field with $[K:\mathbb{Q}]=3$, equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ that is integral, $\Phi$ is a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients (a level ideal $\Phi.\mathrm{level}\neq 0$ together with Satake data $v\mapsto \Phi.a\,v$, $v\mapsto \Phi.b\,v$), $P$ is a real archimedean parameter (either $\mathrm{principal}\ u_1\,a_1\,u_2\,a_2$ with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or $\mathrm{discrete}\ u_0\,n$ with $1\le n$), and $\psi$ is an additive character of the adeles of $\mathbb{Q}$.
--
--   **Eigensystem and ramification data.** Finite sets $S_Q$ of height-one primes of $\mathcal{O}_{\mathbb{Q}}$ and $S_K$ of height-one primes of $\mathcal{O}_K$ are given; `hSQ` asserts that every $p$ with $\Phi.\mathrm{level}\subseteq p$ lies in $S_Q$, and that every prime $\mathfrak{P}$ of $\mathcal{O}_K$ whose contraction to $\mathcal{O}_{\mathbb{Q}}$ is outside $S_Q$ has ramification index $1$; `hSK` asserts $\mathfrak{P}\in S_K$ exactly when the prime below lies in $S_Q$. The hypothesis `hb` requires $\lVert \Phi.b\,p\rVert=1$ for $p\notin S_Q$, and `ha` requires, for every real $\sigma>1$, summability of $p\mapsto \lVert\Phi.a\,p\rVert\,N(p)^{-\sigma}$ over all height-one primes. Also given are $S\subseteq S_Q$ and, for each $p\in S_Q$, a natural number $b_Q(p)$ with `hbQ`: $p^{b_Q(p)}\mid \Phi.\mathrm{level}$ and $p^{b_Q(p)+1}\nmid\Phi.\mathrm{level}$.
--
--   **Realisation and archimedean parameter.** $R$ is a smooth cuspidal realisation at the production pins of $\mathbb{Q}$ for the raw-central normalisation $\Phi.\mathrm{toRawCentral}$ (Satake $b$ divided by the absolute norm): a non-zero function on $\mathrm{GL}_2$ of the adeles, smooth and cuspidal with central character $R.\mathrm{centralChar}$, invariant under the level-$\Phi.\mathrm{level}$ subgroup of the pins, and a Hecke coset eigenfunction with eigenvalues $\Phi.a\,v$ and central eigenvalues $\Phi.b\,v$ outside its exceptional set; `hRc` asserts continuity of $R$ and `hRS` that its exceptional set is contained in $S$. A function $C_{\mathrm{fin}}$ on finite adeles times $\mathrm{GL}_2$ of the adeles is given. The hypotheses `hP1` and `hP2` restrict the principal case of $P$ at a real infinite place: $|\mathrm{Re}(u_1-u_2)|<1$, and for no non-zero integer $m$ is $u_1-u_2=m$ with $a_1-a_2=m+1$ in $\mathbb{Z}/2$. The hypothesis `hRcen` asserts that at each real infinite place $w$ the archimedean component of $R.\mathrm{centralChar}$ (transported along the canonical identification of the top subgroup) is given by exponent $P.\mathrm{centralExponent}+1$ and integer $P.\mathrm{centralSign}$.
--
--   **The parity family.** For each parity $\mathrm{par}:\mathrm{InfinitePlace}\ \mathbb{Q}\to\mathbb{Z}/2$ there are a function $\varphi_{\mathrm{par}}$ on $\mathrm{GL}_2$ of the adeles, archimedean Whittaker functions $W_r(\mathrm{par},w):\mathbb{C}\to\mathbb{C}$ and weights $k_w(\mathrm{par},w)\in\mathbb{Z}$. The hypothesis `hiso` asserts that each $\varphi_{\mathrm{par}}$ is an isotypic cusp form for the pins, central character $R.\mathrm{centralChar}$, level $\Phi.\mathrm{level}$, exceptional set $S$ and eigensystem $\Phi$ (smooth cuspidal automorphic, continuous, invariant under the level subgroup, Hecke eigenfunction with eigenvalue $\Phi.a\,v$ outside $S$ and central eigenvalue $\Phi.\mathrm{toRawCentral}.b\,v$ outside $S$); `hφne` that $\varphi_{\mathrm{par}}\neq0$; `hφKf` that $\varphi_{\mathrm{par}}$ is reproduced by right convolution against some factorizable test function; `hφarch` that at each real place $\varphi_{\mathrm{par}}$ satisfies the predicate `HasArchCharacterAt₀` for the weight character $\mathrm{archWeightCharAt}$ of weight $k_w(\mathrm{par},w)$; `hkw1` and `hkw2` pin these weights to $P$, namely $k_w=\mathrm{signShift}(a_1+\mathrm{par}\,w)+\mathrm{signShift}(a_2+\mathrm{par}\,w)$ in the principal case and $k_w=n+1$ in the discrete case; and `hφW` gives the factorisation of the $\psi_{\mathbb{Q}}$-Whittaker coefficient at $\alpha=1$: for every idele $a$ and every $g$ in the finite-adelic subgroup,
--   $$W_{\varphi_{\mathrm{par}}}(\mathrm{diag}(a,1)\,g)=\Big(\prod_{w}W_r(\mathrm{par},w)\big(a_w\big)\Big)\cdot C_{\mathrm{fin}}(a_{\mathrm{fin}})(g),$$
--   the archimedean components being taken through the embedding of $w.\mathrm{Completion}$ into $\mathbb{C}$.
--
--   **Archimedean Whittaker identities.** `hWr1` gives, in the principal case with $a_1=a_2$ and $\mathrm{par}\,w=a_1$, the reflection $W_r(-t)=(-1)^{a_1}W_r(t)$; `hWr2` gives $W_r(t)=0$ for $t<0$ in the discrete case; `hWr3` gives, in the principal case with $a_1=a_2$ and $\mathrm{par}\,w=a_1+1$, a right half-plane on which the Mellin transform of $t\mapsto (W_r(t)+(-1)^{a_1}W_r(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$; and `hWr4` gives, for $b=\mathrm{par}\,w$ or $b=\mathrm{par}\,w+P.\mathrm{centralSign}$, a right half-plane on which the corresponding symmetrised Mellin transform converges and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$.
--
--   **Base-change twist.** A finite set $T_q$ of primes of $\mathcal{O}_{\mathbb{Q}}$ and an admissible twist $\omega$ of $K$ (idele class character, continuous, unitary) are given with: `hωT`, for $\mathfrak{P}$ above a prime outside $T_q$, $\omega$ is unramified at $\mathfrak{P}$ and $\omega$ of the uniformizer idele equals the formal base-change value $\Phi.b(p)^{f}$, $f$ the inertia degree; `hE`, every $\mathfrak{P}$ above $T_q$ lies in $S_K$; `hωR` and `hωC`, the archimedean components of $\omega$ at real, respectively complex, places are those of $\mathrm{archOfParamR}$, respectively $\mathrm{archOfParamC}$, of $P$.
--
--   **Off-diagonal twist of deep conductor.** An admissible twist $\mu$ of $K$ is given with: `hoff`, there is no admissible twist $\eta$ of $\mathbb{Q}$ such that at every $\mathfrak{P}$ at which $\mu$ is unramified and $\eta$ is unramified below, $\mu$ of the uniformizer idele equals $\eta$ of the uniformizer idele below raised to the inertia degree; `hdepth`, for every $w\in S_K$,
--   $$4\big(\mathrm{count}_w(\Phi.\mathrm{level}\cdot\mathcal{O}_K)+\mathrm{addCharLevel}(\psi_{K,w})+1\big)\le \mathrm{conductorExponentAt}(\mu_w).$$
--   Further, an admissible twist $\chi_A$ of $\mathbb{Q}$ is given with `hχoff` ($\chi_A$ unramified outside $S_Q$), conductor exponents $k_\chi(p)$ at $p\in S_Q$ (`hkχ`), and `hχinf` (trivial archimedean component, exponent $0$ and integer $0$, at each real place); a bound function $c_0$ with `hν`: for $p\in S_Q$ and $w$ in the fibre over $p$, the local component of $\mu\cdot(\chi_A\circ\text{idelic norm})^{-1}$ at $w$ has conductor exponent some $c\le c_0(p)$. The hypothesis `hkfloor` is the explicit lower bound, for each $p\in S_Q$,
--   $$6\Big(b_Q(p)+3\Big(2\sum_{w\mid p}f_w\big(e_w(2(52+3c_0(p))+\ell_w+2)+c_0(p)+\ell_w+1\big)+(52+3c_0(p))\Big)+3\Big)+7\le k_\chi(p),$$
--   where $f_w$, $e_w$ are the inertia degree and ramification index of $w$ over $p$ and $\ell_w=\mathrm{addCharLevel}(\psi_{K,w})$, the sum being over the fibre of $p$. An admissible twist $\nu$ of $K$ is given with `hμν`: $\mu=\nu\cdot(\chi_A\circ\text{idelic norm of the genuine base change})$. Archimedean data $u_R,a_R$ at real places and $u_C,k_C$ at complex places of $K$ describe the archimedean components of $\mu$ through `hcR` and `hcC`.
--
--   **Global additive character.** `hψ` asserts that $\psi$ is a global additive character (trivial on principal adeles, continuous, non-trivial), `hlev` that each local level $\mathrm{addCharLevel}(\psi_v)$ vanishes, and `hψQ` that $\psi^{-1}$ is the standard character $\psi_{\mathbb{Q}}$.
--
--   **The cubic-induction form.** $F$ is a cubic-induction form over $K$ for the production pins of $\mathbb{Q}$ built from the class-representative Siegel set with parameters $(1/2,1,1/2,2)$, the level subgroups $\mathrm{levelOne}\cap$ the finite-adelic subgroup, the Hecke generators and the adelic box, for $\psi$ and $\nu$: a $\mathrm{GL}_3$ automorphic function with central character, cuspidal along both maximal parabolic radicals, together with its global Whittaker function, local Whittaker functions, archimedean Whittaker function and dual Whittaker function, satisfying the Whittaker transformation law, the mirabolic expansion, factorisation outside the bad places, sphericality and level invariance outside the bad places, multiplicity one, moderate growth and $K$-finiteness. The hypothesis `hF0` asserts $F.\mathrm{form}\neq0$ and, at each $v$ unramified in $K$ with $\mathrm{addCharLevel}(\psi_v)=0$, that $F.\mathrm{whittakerLoc}\,v\,1=1$ and that $F.\mathrm{whittakerLoc}\,v$ has the spherical torus values attached to the induced coefficients of $\nu$; `hFc`, `hFw`, `hFdw` assert continuity of the form, the Whittaker function and the dual Whittaker function; `hFg`, `hFdg` assert gauge majorisation (support in a root level and decay by the root-size product and archimedean root sum) of the Whittaker and dual Whittaker functions; `hBad` asserts, for every finite set $T$ of primes of $\mathcal{O}_{\mathbb{Q}}$, that at each bad place $v\in T$ for $(K,\nu)$ the local Whittaker function is right invariant under some open subgroup of $\mathrm{GL}_3$ of the completion, and that it lies in the cyclic subspace generated by any non-zero member of its own cyclic subspace.
--
--   **Good places and uniformizers.** A finite set $S'\supseteq S_Q$ is given with `hgood`: no prime outside $S'$ is a bad place for $(K,\mu)$. Elements $\varpi_p$ of the rings of adic integers are given with `hπ` (non-zero image in the completion for $p\notin S_Q$) and `hϖ` (valuation $\exp(-1)$ for $p\notin S_Q$).
--
--   **The $\mathrm{GL}_3$ local vectors at $S_Q$.** For each $p\in S_Q$ a function $m_P(p)$ on $\mathrm{GL}_3$ of the completion at $p$ is given with: `hmPmem`, $m_P(p)$ lies in the cyclic subspace generated by $g\mapsto \chi_{A,p}(\det g)\,F.\mathrm{whittakerLoc}\,p\,g$; `hmP1`, $m_P(p)\,1=1$; `hW₃admM`, for every open subgroup $U_v$ there is a finite set spanning the $U_v$-right-invariant vectors of the cyclic subspace of $m_P(p)$; `hW₃irrM`, every non-zero member of that cyclic subspace generates $m_P(p)$.
--
--   **A finite-adelic shift.** An element $h_{\mu f}$ of the finite-adelic subgroup is given, identified by `hhμf` with the product over $p\in S'\setminus S_Q$ of the place-embedded scalar matrices $\mathrm{scalarPi}(\varpi_p)^{-\mathrm{inducedLevelAt}(K,\mu,p)}$.
--
--   **$\mathrm{GL}_2$ Whittaker factors and local models.** Functions $W_A(\mathrm{par})$ on $\mathrm{GL}_2(\mathbb{R})$ and $W_f(\mathrm{par})$ on the finite-adelic subgroup are given with `hWAf`: the $\psi_{\mathbb{Q}}$-Whittaker coefficient of $\varphi_{\mathrm{par}}$ at $\alpha=1$ and $g$ equals $W_A(\mathrm{par})(\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{par})(\mathrm{finFactor}\,g)$; `hWfC`: $W_f(\mathrm{par})\,g=C_{\mathrm{fin}}(1)(g)$; `hWf1`: $W_f(\mathrm{par})\,1\neq0$. The hypothesis `hV` asserts, for each $p\in S_Q$, that the local Whittaker space $\mathrm{localSpaceAt}$ of $\varphi_{\mathrm{par}}$ at $p$ (the span of the local Whittaker functions of the right translates of $\varphi_{\mathrm{par}}$) is irreducible (every non-zero member generates the whole space under right translation), admissible (for every open subgroup of $\mathrm{GL}_2$ of the completion the right-invariant vectors are spanned by a finite set) and smooth (every member is right invariant under some open subgroup). An element $w_0\in\mathrm{GL}_2(\mathbb{Q})$ is given with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, together with functions $W_{fd}(\mathrm{par})$ on the finite-adelic subgroup defined by `hWfd`: $W_{fd}(\mathrm{par})(g_f)=\lVert\det g_f\rVert_{\mathbb{A}}\cdot W_f(\mathrm{par})\big(\mathrm{finFactor}(w_0\cdot{}^{t}g_f^{-1})\big)$.
--
--   **Local data at the distinguished place.** Finally a parity $\mathrm{par}$ is fixed, a prime $p\in S_Q$, a function $w_{2b}$ belonging to the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$, and an element $h_2$ of $\mathrm{GL}_2$ of the adeles whose $p$-component is trivial.
--
--   **Conclusion.** Under these hypotheses there exist $n_P\in\mathbb{N}$, coefficients $c_P:\mathrm{Fin}\,n_P\to\mathbb{C}$, local elements $x_P:\mathrm{Fin}\,n_P\to\mathrm{GL}_2(\mathbb{Q}_p)$, and functions $w_A$ on $\mathrm{GL}_2(\mathbb{R})$, $w_f$ on the finite-adelic subgroup and $w_p$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ such that, writing $\iota_p$ for the place embedding at $p$ and
--   $$\varphi^{\circ}(g)=\sum_{j}c_P(j)\,\lVert\det(g\,\iota_p(x_P(j)))\rVert_{\mathbb{A}}^{-1/2}\,\varphi_{\mathrm{par}}\big(g\,\iota_p(x_P(j))\,h_2\big),$$
--   the following hold:
--
--   1. $w_f\circ\mathrm{finFactor}$ is blind to the $p$-component: $w_f(\mathrm{finFactor}(g\,\iota_p(x)))=w_f(\mathrm{finFactor}\,g)$ for every $x\in\mathrm{GL}_2(\mathbb{Q}_p)$ and every adelic $g$;
--
--   2. $w_f$ is measurable;
--
--   3. for every adele $t$ with vanishing archimedean component and every adelic $g$,
--   $$w_f\big(\mathrm{finFactor}(n(t)\,g)\big)=\big(\psi^{-1}(t)\,\psi_p(t_p)\big)\,w_f(\mathrm{finFactor}\,g),$$
--   where $n(t)$ is the upper unipotent with entry $t$ and $\psi_p$ is the local component of $\psi$ at $p$, so the $p$-factor is divided out;
--
--   4. $w_p$ is a $\psi_{\mathbb{Q},p}$-Whittaker function: $w_p(n(t)\,y)=\psi_{\mathbb{Q},p}(t)\,w_p(y)$ for $t\in\mathbb{Q}_p$ and $y\in\mathrm{GL}_2(\mathbb{Q}_p)$;
--
--   5. $w_p\neq0$;
--
--   6. there is a $w_1$ in the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$ with $w_p(y)=\mathrm{modulus}(\det y)^{-1/2}\,w_1(y)$ for all $y$;
--
--   7. for every adelic $g$, the $\psi^{-1}$-Whittaker coefficient of $\varphi^{\circ}$ at $\alpha=1$ and $g$, taken for the production pins of $\mathbb{Q}$, equals
--   $$w_p\big(g_p\big)\cdot\big(w_A(\mathrm{ratArchGL2}\,g)\cdot w_f(\mathrm{finFactor}\,g)\big);$$
--
--   8. that $\psi^{-1}$-Whittaker coefficient of $\varphi^{\circ}$ at $\alpha=1$ is non-zero at some adelic $g$.
--
--   This is the purification step in the Rankin–Selberg phase of the Langlands–Tunnell argument: the finite Whittaker factor of the isotypic cusp form $\varphi_{\mathrm{par}}$ is only given as a sum of $p$-slot times complement terms, and the statement produces a finite combination of right translates at $p$ whose Whittaker coefficient splits as a single product of a non-zero $p$-component, an archimedean factor and a $p$-blind finite factor. It is invoked by the statements producing a finite translate on which the local Rankin–Selberg indicator integral is non-zero and a combination of pure translates with non-vanishing global Rankin–Selberg integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.lean

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

open MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker in

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
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
    (h₂ : AdelicGL2 (𝓞 ℚ) ℚ) (hh₂ : localAt ℚ p h₂ = 1) :
    ∃ (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
      (wA : GL (Fin 2) ℝ → ℂ) (wf : finiteAdelicGL2Subgroup ℚ → ℂ) (wp : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        wf (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = wf (RSCarrier.finFactor g)) ∧
      Measurable wf ∧
      (∀ (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, wf (RSCarrier.finFactor (unipotentGL2 t * g)) =
          (ψ⁻¹ t * LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p)) * wf (RSCarrier.finFactor g)) ∧
      (∀ (t : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)),
        wp (unipotent t * y) = NumberField.StandardAddChar.psiLocal ℚ p t * wp y) ∧
      wp ≠ 0 ∧
      (∃ w₁ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
        ∀ y : GL (Fin 2) (p.adicCompletion ℚ), wp y = ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₁ y) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹
            (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (xP j) * h₂))) 1 g =
          wp (localAt ℚ p g) * (wA (ratArchGL2 g) * wf (RSCarrier.finFactor g))) ∧

      (∃ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹
            (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (xP j) * h₂))) 1 g ≠ 0) := by sorry
