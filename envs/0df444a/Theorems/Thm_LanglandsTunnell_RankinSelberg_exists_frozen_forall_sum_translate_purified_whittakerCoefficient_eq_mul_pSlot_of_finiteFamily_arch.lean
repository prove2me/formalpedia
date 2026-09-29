-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
-- name    : LanglandsTunnell.RankinSelberg.exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/7cb455be-9d76-5c8d-85ab-7b43a0f9bda2
-- title:
--   Purified p-slot splitting of Whittaker coefficients of p-adic translates
-- statement:
--   Throughout, $K$ is a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, with $\operatorname{finrank}_{\mathbb{Q}} K = 3$; $\Phi$ is a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients (a nonzero level ideal together with families $\Phi.a$, $\Phi.b$ indexed by the finite places). Notation: $\iota_p$ denotes [`UnramifiedWhittaker.placeEmbed ℚ p`](def/UnramifiedWhittaker_HeckeRecursion.html#L47), $g_p :=$ `localAt ℚ p g`, $g_\infty :=$ `ratArchGL2 g` (the real $GL_2$-component), $g_f :=$ [`RSCarrier.finFactor g`](def/LanglandsTunnell_RSCarrierSplit.html#L17) (the finite-adelic factor), $u(t) :=$ `unipotentGL2 t`, and `whittakerCoefficient` is the integral $\int \varphi(u(x)g)\,\chi(-\alpha x)$ over the adeles against the Haar measure of the carrier pins conditioned on the adelic box. The carrier data `productionPinsGeneral ℚ` is `productionPinsOf` applied to the class-representative Siegel set with parameters $(1/2,1,1/2,2)$, the level subgroups `levelOne ⊓ finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen` and the adelic box; both spellings occur in the statement and denote the same data.
--
--   *Away data on the $GL_2$ side.* A finite set $S_Q$ of primes of $\mathcal{O}_{\mathbb{Q}}$ is given, with `hSQ`: every prime containing $\Phi$'s level lies in $S_Q$, and every prime $\mathfrak{P}$ of $K$ whose contraction to $\mathbb{Q}$ lies outside $S_Q$ has ramification index $1$; `hb`: $\|\Phi.b(p)\| = 1$ for $p \notin S_Q$; `ha`: for every real $\sigma > 1$ the series $\sum_p \|\Phi.a(p)\| N(p)^{-\sigma}$ converges. A finite set $S_K$ of primes of $K$ is characterised by `hSK` as the set of primes above $S_Q$. Further: a real archimedean parameter $P$ (either `principal` $(u_1,a_1,u_2,a_2)$ with $a_i \in \mathbb{Z}/2$, or `discrete` $(u_0,n)$ with $n \ge 1$); a finite $S \subseteq S_Q$; a smooth cuspidal realisation $R$ at `productionPinsGeneral ℚ` of the rescaled eigensystem $\Phi.\mathrm{toRawCentral}$ (whose $b$-coefficients are $N(v)^{-1}\Phi.b(v)$), with `hRc` its underlying function continuous and `hRS` its exceptional set contained in $S$; and a function $C_{\mathrm{fin}}$ of a finite adele and an adelic $GL_2$-element.
--
--   *Archimedean constraints.* `hP1` and `hP2` require, in the principal case $P =$ `principal` $(u_1,a_1,u_2,a_2)$ (quantified over real infinite places of $\mathbb{Q}$), that $|\mathrm{Re}(u_1-u_2)| < 1$ and that for no nonzero integer $m$ with $u_1-u_2 = m$ does $a_1 - a_2 = m+1$ in $\mathbb{Z}/2$. `hRcen` says that the central character of $R$, transported along `Subgroup.topEquiv.symm` to the full idele class group, has at each real place the archimedean shape `IsArchCompAt` with exponent $P.\mathrm{centralExponent}+1$ and sign $P.\mathrm{centralSign}$.
--
--   *The finite family of $GL_2$ forms.* For every parity vector $\mathrm{par} \colon \mathrm{InfinitePlace}\,\mathbb{Q} \to \mathbb{Z}/2$ there are given a function $\varphi_v(\mathrm{par})$ on adelic $GL_2$, archimedean Whittaker functions $W_r(\mathrm{par},w)\colon \mathbb{C}\to\mathbb{C}$ and integers $k_w(\mathrm{par},w)$, subject to: `hiso`, that $\varphi_v(\mathrm{par})$ is a $\Phi$-isotypic cusp form at level $\Phi.\mathrm{level}$ with exceptional set $S$ and central character $R.\mathrm{centralChar}$ (smooth cuspidal automorphic, continuous, invariant under the level subgroup, Hecke coset eigenfunction with eigenvalue $\Phi.a(v)$ off $S$, and central eigenfunction with eigenvalue $\Phi.\mathrm{toRawCentral}.b(v)$ off $S$); `hφne`, that it is nonzero; `hφKf`, that it is fixed by right convolution with some factorizable test function; `hφarch`, that it satisfies `HasArchCharacterAt₀` at each real place $w$ with the character `archWeightCharAt hw (kw par w)`, the $k_w(\mathrm{par},w)$-th power of the basic weight-one archimedean character; `hkw1` and `hkw2`, which fix the weights in terms of $P$: in the principal case $k_w(\mathrm{par},w) = \mathrm{signShift}(a_1+\mathrm{par}(w)) + \mathrm{signShift}(a_2+\mathrm{par}(w))$ as complex numbers, and in the discrete case $k_w(\mathrm{par},w) = n+1$; and `hφW`, the factorisation of the $\psi_{\mathbb{Q}}$-Whittaker coefficient at $\alpha = 1$: for every idele $a$ and every $g$ in `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection),
--   $$W_{\varphi_v(\mathrm{par})}(\mathrm{diagOne}(a)\,g) = \Big(\prod_{w} W_r(\mathrm{par},w)\big(\mathrm{extensionEmbedding}_w(a_\infty(w))\big)\Big)\cdot C_{\mathrm{fin}}(a_{\mathrm{fin}}, g).$$
--   The hypotheses `hWr1`–`hWr4` constrain $W_r$: a reflection law $W_r(\mathrm{par},w)(-t) = (-1)^{a_1}W_r(\mathrm{par},w)(t)$ in the principal case with $a_2 = a_1$ and $\mathrm{par}(w) = a_1$; vanishing of $W_r(\mathrm{par},w)$ on the negative reals in the discrete case; and two Mellin identities, valid and convergent in a right half-plane — for $\mathrm{par}(w) = a_1+1$ in the principal case with $a_2 = a_1$,
--   $$\mathrm{mellin}\Big(t \mapsto \tfrac{W_r(\mathrm{par},w)(t) + (-1)^{a_1}W_r(\mathrm{par},w)(-t)}{t}\Big)(s) = \frac{2s+u_1+u_2-1}{4\pi}\,\big(P.\mathrm{twist}\,0\,a_1\big).\mathrm{archFactor}(s),$$
--   and, for $b$ equal to $\mathrm{par}(w)$ or to $\mathrm{par}(w)+P.\mathrm{centralSign}$, the same Mellin transform with $(-1)^{b}$ in place of $(-1)^{a_1}$ equals $\big(P.\mathrm{twist}\,0\,b\big).\mathrm{archFactor}(s)$.
--
--   *Characters over $K$ and the cubic-induction form.* A finite set $T_q$ of primes of $\mathbb{Q}$ and an admissible twist $\omega$ of $K$ (an idele class character that is continuous and unitary) are given with: `hωT`, $\omega$ unramified at every $\mathfrak{P}$ over the complement of $T_q$, where $\omega$ of the uniformiser idele equals the base-change coefficient $(\mathrm{formalBaseChange}\,\mathbb{Q}\,K\,\Phi).b(\mathfrak{P}) = \Phi.b(p)^{f(\mathfrak{P}/p)}$; `hE`, every $\mathfrak{P}$ above $T_q$ lies in $S_K$; `hωR` and `hωC`, the archimedean components of $\omega$ at real and complex places given by `IsArchCompAt` with the exponent and sign of $P$, respectively the exponent and twist of $P.\mathrm{baseChange}$. A second admissible twist $\mu$ of $K$ is given with `hoff`: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_p)^{f(\mathfrak{P}/p)}$ at all $\mathfrak{P}$ where both $\mu$ and $\eta$ are unramified; and `hdepth`: for every $\mathfrak{P} \in S_K$,
--   $$4\big(\mathrm{count}_{\mathfrak{P}}(\Phi.\mathrm{level}\cdot\mathcal{O}_K) + \mathrm{addCharLevel}(\psi_{K,\mathfrak{P}}) + 1\big) \le \mathrm{conductorExponentAt}(\mathrm{localChar}\,\mu\,\mathfrak{P}).$$
--   An admissible twist $\chi_A$ of $\mathbb{Q}$ is given, unramified outside $S_Q$ (`hχoff`), with conductor exponents $k_\chi(p)$ at $p \in S_Q$ (`hkχ`) and trivial archimedean shape (exponent $0$, sign $0$) at real places (`hχinf`). The function $c_0$ bounds, by `hν`, the conductor exponents of the local components of $\mu\cdot(\chi_A\circ \mathrm{idelicNorm}\,\mathrm{genuineBaseChange})^{-1}$ at all places of $K$ in the fibre over each $p \in S_Q$. The function $b_Q$ records, by `hbQ`, the exact exponent of $p$ in $\Phi.\mathrm{level}$ for $p \in S_Q$, and `hkfloor` imposes the explicit lower bound
--   $$6\Big(b_Q(p) + 3\Big(2\Big(\sum_{\mathfrak{P}\mid p} f_{\mathfrak{P}}\big(e_{\mathfrak{P}}\big(2(52+3c_0(p)) + \ell_{\mathfrak{P}} + 2\big) + c_0(p) + \ell_{\mathfrak{P}} + 1\big) + \big(52+3c_0(p)\big)\Big)\Big)+3\Big)+7 \le k_\chi(p)$$
--   for $p \in S_Q$, where $f_{\mathfrak{P}}$, $e_{\mathfrak{P}}$ are the inertia degree and ramification index and $\ell_{\mathfrak{P}} = \mathrm{addCharLevel}(\psi_{K,\mathfrak{P}})$, the sum being over the prime fibre. An admissible twist $\nu$ of $K$ is given with $\mu = \nu\cdot(\chi_A\circ\mathrm{idelicNorm}\,\mathrm{genuineBaseChange})$ (`hμν`), and data $u_R, a_R$ (real places), $u_C, k_C$ (complex places) describing the archimedean components of $\mu$ by `hcR`, `hcC`. A global additive character $\psi$ of the adeles of $\mathbb{Q}$ is given (trivial on $\mathbb{Q}$, continuous, nontrivial) with all local levels zero (`hlev`) and $\psi^{-1} = \psi_{\mathbb{Q}}$ (`hψQ`). Finally $F$ is a `CubicInductionForm` over $K$ at the production pins with character $\psi$ and twist $\nu$ — a cuspidal $GL_3$ datum with form, global and local Whittaker functions, central character, and dual Whittaker function, subject to the structure's axioms — together with: `hF0`, that $F.\mathrm{form} \ne 0$ and that at each place $v$ unramified in $K$ with local additive character of level $0$ one has $F.\mathrm{whittakerLoc}_v(1) = 1$ and spherical torus values for the induced coefficients of $\nu$; `hFc`, `hFw`, `hFdw`, continuity of form, Whittaker and dual Whittaker; `hFg`, `hFdg`, gauge majorisation `IsGaugeMajorised3` of the latter two; and `hBad`, asserting for every finite set $T$ of primes that at each bad place $v \in T$ for $(K,\nu)$ (ramified in $K$, or $\nu$ ramified above $v$) the local Whittaker function is right invariant under some open subgroup of $GL_3(\mathbb{Q}_v)$ and lies in the cyclic subspace generated by every nonzero element of its own cyclic subspace.
--
--   *Frozen auxiliary data.* A finite $S' \supseteq S_Q$ is given with no bad place for $(K,\mu)$ outside $S'$ (`hgood`); local elements $\varpi_p$ of the completed valuation rings which, for $p \notin S_Q$, are nonzero of valuation $\exp(-1)$, i.e. uniformisers (`hπ`, `hϖ`). For each $p \in S_Q$ a function $m_P(p)$ on $GL_3(\mathbb{Q}_p)$ is given which lies in the $GL_3$ cyclic subspace generated by $g \mapsto \mathrm{localChar}(\chi_A)_p(\det g)\cdot F.\mathrm{whittakerLoc}_p(g)$ (`hmPmem`), satisfies $m_P(p)(1) = 1$ (`hmP1`), is admissible in the sense that for every open subgroup there is a finite set spanning all right-invariant vectors of its cyclic subspace (`hW₃admM`), and generates: $m_P(p)$ lies in the cyclic subspace of every nonzero element of its own cyclic subspace (`hW₃irrM`). An element `hμf` of `finiteAdelicGL2Subgroup ℚ` is given which, by `hhμf`, equals the product over $p \in S'\setminus S_Q$ of the $p$-adic embeddings of $\mathrm{scalarPi}(\varpi_p)^{-\mathrm{inducedLevelAt}(K,\mu,p)}$.
--
--   *Archimedean/finite splitting of the family.* Functions $W_A(\mathrm{par})$ on $GL_2(\mathbb{R})$ and $W_f(\mathrm{par})$ on the finite-adelic subgroup are given with `hWAf`: the $\psi_{\mathbb{Q}}$-Whittaker coefficient of $\varphi_v(\mathrm{par})$ at $\alpha = 1$ equals $W_A(\mathrm{par})(g_\infty)\cdot W_f(\mathrm{par})(g_f)$; `hWfC`: $W_f(\mathrm{par})(g) = C_{\mathrm{fin}}(1,g)$; and `hWf1`: $W_f(\mathrm{par})(1) \ne 0$. The hypothesis `hV` asserts, for every parity and every $p \in S_Q$, that the local Whittaker space `localSpaceAt` of $\varphi_v(\mathrm{par})$ at $p$ is irreducible (every nonzero member generates it under right translation), admissible (for each open subgroup, a finite set spanning the vectors invariant under it), and smooth (each member is fixed by some open subgroup). An element $w_0 \in GL_2(\mathbb{Q})$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is given, and $W_{fd}(\mathrm{par})(g_f) := \|\det g_f\|_{\mathbb{A}}\cdot W_f(\mathrm{par})\big((w_0\cdot{}^{t}g_f^{-1})_f\big)$ (`hWfd`), $w_0$ being mapped into the adelic group by `globalPoints` and ${}^{t}(\cdot)^{-1}$ being `transposeInvN`.
--
--   *The local datum at $p$ and the purifier.* A parity $\mathrm{par}$, a prime $p \in S_Q$, an element $w_{2b}$ of the local Whittaker space of $\varphi_v(\mathrm{par})$ at $p$, and an element $h_2$ of adelic $GL_2$ with trivial $p$-component are fixed. Further there are given a natural number $n_P$, coefficients $c_P \colon \mathrm{Fin}\,n_P \to \mathbb{C}$ and elements $x_P \colon \mathrm{Fin}\,n_P \to GL_2(\mathbb{Q}_p)$, together with functions $w_A$ on $GL_2(\mathbb{R})$, $w_f$ on the finite-adelic subgroup and $w_p$ on $GL_2(\mathbb{Q}_p)$ such that: $w_f(g\,\iota_p x)_f = w_f(g_f)$ for all $p$-adic $x$ (`hwfp`); $w_f$ is measurable (`hwfm`); for every adele $t$ with vanishing archimedean component, $w_f\big((u(t)g)_f\big) = \psi^{-1}(t)\,\psi_{\mathrm{loc}}(\psi,p)(t_p)\,w_f(g_f)$ (`hwfn`); $w_p(u(t)y) = \psi_{\mathbb{Q},p}(t)\,w_p(y)$ (`hwpn`); $w_p \ne 0$ (`hwp0`); $w_p(y) = |\det y|_p^{-1/2}\,w_1(y)$ for some $w_1$ in the local Whittaker space of $\varphi_v(\mathrm{par})$ at $p$ (`hwpV`); and `hpure`: the $\psi^{-1}$-Whittaker coefficient at $\alpha = 1$ of the purified function
--   $$\varphi^{\circ}(g) = \sum_j c_P(j)\,\big\|\det\big(g\,\iota_p x_P(j)\big)\big\|_{\mathbb{A}}^{-1/2}\,\varphi_v(\mathrm{par})\big(g\,\iota_p x_P(j)\,h_2\big)$$
--   equals $w_p(g_p)\cdot\big(w_A(g_\infty)\,w_f(g_f)\big)$ for all $g$.
--
--   **Conclusion.** There exist functions $W_A', W_{dA}'$ on $GL_2(\mathbb{R})$ and $W_f', W_{df}'$ on `finiteAdelicGL2Subgroup ℚ` such that:
--
--   (i) $W_f'$ and $W_{df}'$ are blind to the $p$-component: $W_f'\big((g\,\iota_p x)_f\big) = W_f'(g_f)$ and likewise for $W_{df}'$, for all $x \in GL_2(\mathbb{Q}_p)$ and all $g$;
--
--   (ii) $W_f'$ and $W_{df}'$ are measurable;
--
--   (iii) for every adele $t$ with vanishing archimedean component and every $g$,
--   $$W_f'\big((u(t)g)_f\big) = \psi^{-1}(t)\,\psi_{\mathrm{loc}}(\psi,p)(t_p)\,W_f'(g_f), \qquad W_{df}'\big((u(t)g)_f\big) = \psi(t)\,\psi_{\mathrm{loc}}(\psi,p)(t_p)^{-1}\,W_{df}'(g_f);$$
--
--   (iv) and for every finite family, that is, for every $n \in \mathbb{N}$, $c \colon \mathrm{Fin}\,n \to \mathbb{C}$ and $x \colon \mathrm{Fin}\,n \to GL_2(\mathbb{Q}_p)$, the double combination
--   $$\varphi_{c,x}(g) := \sum_i c_i \sum_j c_P(j)\,\big\|\det\big(g\,\iota_p x_i\,\iota_p x_P(j)\big)\big\|_{\mathbb{A}}^{-1/2}\,\varphi_v(\mathrm{par})\big(g\,\iota_p x_i\,\iota_p x_P(j)\,h_2\big)$$
--   satisfies the following five assertions: it is continuous; it is left invariant under the rational points, $\varphi_{c,x}(\gamma g) = \varphi_{c,x}(g)$ for all $\gamma \in GL_2(\mathbb{Q})$ (embedded by `globalPoints`) and all $g$; it is of moderate growth, i.e. there are real $C, r$ with $\|\varphi_{c,x}(g)\| \le C\,\mathrm{detNorm}(g)^r$ for all $g$, where $\mathrm{detNorm}$ is the idele norm of the determinant; its $\psi^{-1}$-Whittaker coefficient at $\alpha = 1$ splits as
--   $$W^{\psi^{-1}}_{\varphi_{c,x}}(g) = \Big(\sum_i c_i\, w_p(g_p\,x_i)\Big)\cdot\big(W_A'(g_\infty)\,W_f'(g_f)\big);$$
--   and the $\psi$-Whittaker coefficient at $\alpha = 1$ of the reflected function $g \mapsto \varphi_{c,x}({}^{t}g^{-1})$ splits as
--   $$\Big(\sum_i c_i\, w_p\big((w_0)_p\,{}^{t}(g_p)^{-1}\,x_i\big)\Big)\cdot\big(W_{dA}'(g_\infty)\,W_{df}'(g_f)\big),$$
--   where $(w_0)_p$ is the $p$-component of the image of $w_0$ under `globalPoints`. In both Whittaker coefficients the carrier data are the production pins spelled out with the class-representative Siegel set of parameters $(1/2,1,1/2,2)$.
--
--   This is a bookkeeping step in the Rankin–Selberg analysis used for the converse-theorem input to the Langlands–Tunnell argument: it freezes the archimedean and away-from-$p$ factors of a purified test vector and shows that, for every finite combination of $p$-adic right translates, the global Whittaker coefficient and its reflected companion split as a local $p$-slot against those frozen complements, with the combination remaining continuous, automorphic and of moderate growth. It is used by the statements producing nonvanishing and fundamental-domain factorisations of the global Rankin–Selberg integral for members of the finite family of $GL_2$ forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
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
    (h₂ : AdelicGL2 (𝓞 ℚ) ℚ) (hh₂ : localAt ℚ p h₂ = 1)

    (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
    (wA : GL (Fin 2) ℝ → ℂ) (wf : finiteAdelicGL2Subgroup ℚ → ℂ) (wp : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwfp : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      wf (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = wf (RSCarrier.finFactor g))
    (hwfm : Measurable wf)
    (hwfn : ∀ (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, wf (RSCarrier.finFactor (unipotentGL2 t * g)) =
        (ψ⁻¹ t * LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p)) * wf (RSCarrier.finFactor g))
    (hwpn : ∀ (t : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)),
      wp (unipotent t * y) = NumberField.StandardAddChar.psiLocal ℚ p t * wp y)
    (hwp0 : wp ≠ 0)
    (hwpV : ∃ w₁ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
      ∀ y : GL (Fin 2) (p.adicCompletion ℚ), wp y = ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₁ y)
    (hpure : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹
          (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (xP j) * h₂))) 1 g =
        wp (localAt ℚ p g) * (wA (ratArchGL2 g) * wf (RSCarrier.finFactor g))) :
    ∃ (WA' WdA' : GL (Fin 2) ℝ → ℂ) (Wf' Wdf' : finiteAdelicGL2Subgroup ℚ → ℂ),

      (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wf' (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wf' (RSCarrier.finFactor g)) ∧
      (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wdf' (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wdf' (RSCarrier.finFactor g)) ∧
      Measurable Wf' ∧ Measurable Wdf' ∧

      (∀ (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wf' (RSCarrier.finFactor (unipotentGL2 t * g)) =
          (ψ⁻¹ t * LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p)) * Wf' (RSCarrier.finFactor g)) ∧
      (∀ (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wdf' (RSCarrier.finFactor (unipotentGL2 t * g)) =
          (ψ t * (LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p))⁻¹) * Wdf' (RSCarrier.finFactor g)) ∧

      ∀ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → GL (Fin 2) (p.adicCompletion ℚ)),
        Continuous (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) ∧
        (∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) (globalPoints (𝓞 ℚ) ℚ γ * g) = (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) g) ∧
        (∃ C r : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖(fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) g‖ ≤ C * detNorm g ^ r) ∧

        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹ (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) 1 g =
            (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ i, c i * wp (y * x i)) (localAt ℚ p g) * (WA' (ratArchGL2 g) * Wf' (RSCarrier.finFactor g))) ∧

        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ (fun g => (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) (transposeInvN (Fin 2) g)) 1 g =
            (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ i, c i * wp (y * x i)) ((localAt ℚ p (globalPoints (𝓞 ℚ) ℚ w₀)) * transposeInvN (Fin 2) (localAt ℚ p g)) *
              (WdA' (ratArchGL2 g) * Wdf' (RSCarrier.finFactor g))) := by sorry
