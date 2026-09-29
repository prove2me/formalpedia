-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_gl3Translates_sum_rsFinIntegral_cells_eq_const_and_dual_eq_rootNumberMonomial_of_finWhittaker_one_ne_zero_of_localSpaceAt_of_member_of_fe32_normPin_twisted_offSQ_archPsi_bump_levelShift_global
-- name    : LanglandsTunnell.RankinSelberg.exists_gl3Translates_sum_rsFinIntegral_cells_eq_const_and_dual_eq_rootNumberMonomial_of_finWhittaker_one_ne_zero_of_localSpaceAt_of_member_of_fe32_normPin_twisted_offSQ_archPsi_bump_levelShift_global
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/2034d7ff-b3e1-5311-9bec-08769e4e0f50
-- title:
--   Finite GL₃-translate family: constant integral and dual root number
-- statement:
--   **Setting.** Let $K$ be a number field, with $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra; the hypothesis `_hdeg` records that $\dim_{\mathbb Q}K=3$. Let $\Phi$ be a Hecke eigensystem for $\mathbb Q$ with complex coefficients, that is, a nonzero level ideal `Φ.level` together with families `Φ.a`, `Φ.b` indexed by the finite places. Let `SQ` be a finite set of primes of $\mathcal O_{\mathbb Q}$. The hypothesis `hSQ` has two clauses: every prime $p$ with $\mathtt{Φ.level}\subseteq p$ lies in `SQ`, and every prime $\mathfrak P$ of $K$ whose restriction to $\mathcal O_{\mathbb Q}$ is outside `SQ` has ramification index $1$. Further, `hb` requires $\|\mathtt{Φ.b}\,p\|=1$ for $p\notin\mathtt{SQ}$, and `ha` requires, for every $\sigma>1$, the summability of $\|\mathtt{Φ.a}\,p\|\,N(p)^{-\sigma}$ over the finite places of $\mathbb Q$. A finite set `SK` of primes of $K$ is fixed by `hSK`: $\mathfrak P\in\mathtt{SK}$ if and only if $\mathfrak P$ lies over `SQ`. Let $P$ be a real archimedean parameter, i.e. either `principal` $(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb C$, $a_i\in\mathbb Z/2$, or `discrete` $(u_0,n)$ with $n\ge 1$; the hypotheses `hP1` and `hP2` state, for each real infinite place of $\mathbb Q$, that in the principal case $|\mathrm{Re}(u_1-u_2)|<1$, and that if $u_1-u_2$ is a nonzero integer $p$ then $a_1-a_2\neq p+1$ in $\mathbb Z/2$.
--
--   **The $\mathrm{GL}_2$ side.** A finite set $S\subseteq\mathtt{SQ}$ is given (`hS`), together with a smooth cuspidal realisation $R$ of the renormalised eigensystem `Φ.toRawCentral` (the system with $b$ replaced by $N(v)^{-1}\mathtt{Φ.b}\,v$) for the carrier pins `productionPinsGeneral ℚ`, with `hRc` asserting continuity of `R.toFun` and `hRS` that `R.exceptionalSet` $\subseteq S$; a function `Cfin` on pairs (finite adele, adelic $\mathrm{GL}_2$ element) is fixed. The hypothesis `hRcen` states that at each real place $w$ the central character of $R$, transported to the full idele group, has archimedean component of exponent $P.\mathrm{centralExponent}+1$ and sign $P.\mathrm{centralSign}$ in the sense of `IsArchCompAt`.
--
--   A parity-indexed family is given: functions $\varphi_{\mathrm{par}}$ on the adelic $\mathrm{GL}_2$, archimedean radial functions $\mathrm{Wr}_{\mathrm{par},w}$ and integers $k_{\mathrm{par},w}$, indexed by $\mathrm{par}:\mathrm{InfinitePlace}(\mathbb Q)\to\mathbb Z/2$. The hypotheses on them are: `hiso`, that each $\varphi_{\mathrm{par}}$ is an `IsIsotypicCuspFormAt` vector for `productionPinsGeneral ℚ`, central character `R.centralChar`, level `Φ.level`, exceptional set $S$ and eigensystem $\Phi$ (smooth cuspidality, continuity, level invariance, Hecke and central eigenvalue relations off $S$); `hφne`, that $\varphi_{\mathrm{par}}\neq 0$; `hφKf`, that each $\varphi_{\mathrm{par}}$ is reproduced by right convolution with some factorizable test function; `hφarch`, that at each real place $\varphi_{\mathrm{par}}$ transforms under `archWeightCharAt hw (kw par w)` in the sense of the predicate `HasArchCharacterAt₀`; `hkw1` and `hkw2`, computing $k_{\mathrm{par},w}$ as $\mathrm{signShift}(a_1+\mathrm{par}(w))+\mathrm{signShift}(a_2+\mathrm{par}(w))$ in the principal case and as $n+1$ in the discrete case; `hφW`, the factorisation of the first Whittaker coefficient for `productionPinsGeneral ℚ` and $\psi_{\mathbb Q}$: for every idele $a$ and every $g$ in the finite adelic $\mathrm{GL}_2$ subgroup, the coefficient at $\mathrm{diag}(a,1)g$ equals $\bigl(\prod_w \mathrm{Wr}_{\mathrm{par},w}(a_w)\bigr)\cdot\mathtt{Cfin}(a_{\mathrm{fin}})(g)$, the $a_w$ being the images of the infinite components of $a$ under `extensionEmbedding`. Finally four archimedean hypotheses on $\mathrm{Wr}$: `hWr1`, in the principal case with $a_2=a_1$ and $\mathrm{par}(w)=a_1$, the parity relation $\mathrm{Wr}_{\mathrm{par},w}(-t)=(-1)^{a_1}\mathrm{Wr}_{\mathrm{par},w}(t)$; `hWr2`, in the discrete case, vanishing on $t<0$; `hWr3`, in the principal case with $a_2=a_1$ and $\mathrm{par}(w)=a_1+1$, convergence of the Mellin transform of $t\mapsto(\mathrm{Wr}_{\mathrm{par},w}(t)+(-1)^{a_1}\mathrm{Wr}_{\mathrm{par},w}(-t))/t$ in some right half-plane and its evaluation as $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$; `hWr4`, for $b\in\{\mathrm{par}(w),\ \mathrm{par}(w)+P.\mathrm{centralSign}\}$, the same Mellin transform with $(-1)^{b}$ in place of $(-1)^{a_1}$ equals the archimedean factor of $P.\mathrm{twist}\,0\,b$.
--
--   **Twisting characters.** A finite set `Tq` of primes of $\mathbb Q$ and a character $\omega$ of the ideles of $K$ are given with $\omega$ admissible (`hω`: idele class character, continuous, unitary); `hωT` requires that for $\mathfrak P$ over primes outside `Tq` the character $\omega$ is unramified at $\mathfrak P$ and $\omega$ of the uniformiser idele equals the $b$-coefficient of the formal base change `formalBaseChange ℚ K Φ` at $\mathfrak P$, and `hE` that the primes of $K$ over `Tq` lie in `SK`; `hωR` and `hωC` prescribe the archimedean components of $\omega$ at the real and complex places of $K$ through `archOfParamR K P` (the constant family $P$) and `archOfParamC K P` (the constant family $P.\mathrm{baseChange}$). A second admissible character $\mu$ of the ideles of $K$ is given (`hμ`) subject to `hoff`, which states that $\mu$ is not of norm type: there is no admissible idele class character $\eta$ of $\mathbb Q$ with $\mu(\varpi_{\mathfrak P})=\eta(\varpi_{p})^{f(\mathfrak P/p)}$ at all $\mathfrak P$ where both are unramified. The hypothesis `hdepth` expresses deep ramification of $\mu$ above `SK`: for every $w\in\mathtt{SK}$,
--   $$4\bigl(\mathrm{ord}_w(\mathtt{Φ.level}\,\mathcal O_K)+\mathrm{addCharLevel}(\psi_{K,w})+1\bigr)\le \mathrm{conductorExponentAt}\,w(\mu_w).$$
--
--   An auxiliary admissible character $\chi_A$ of the ideles of $\mathbb Q$ (`hχA`) is given, unramified outside `SQ` (`hχoff`), with conductor exponents $k_\chi(p)$ at $p\in\mathtt{SQ}$ (`hkχ`) and trivial archimedean component at the real places (`hχinf`). Bookkeeping functions are fixed: $c_0$ with `hν`, bounding by $c_0(p)$ the conductor exponents at the primes of $K$ over $p\in\mathtt{SQ}$ of the local characters of $\mu\cdot(\chi_A\circ\mathrm{idelicNorm})^{-1}$; $b_{\mathbb Q}$ with `hbQ`, the exact exponent of $p$ in `Φ.level` for $p\in\mathtt{SQ}$; and `hkfloor`, an explicit lower bound for $k_\chi(p)$ in terms of $b_{\mathbb Q}(p)$, $c_0(p)$, the inertia degrees and ramification indices in the fibre over $p$ and the levels $\mathrm{addCharLevel}(\psi_{K,w})$, namely $6\bigl(b_{\mathbb Q}(p)+3\bigl(2\bigl(\sum_{w\mid p} f_w(e_w(2(52+3c_0(p))+\mathrm{addCharLevel}(\psi_{K,w})+2)+c_0(p)+\mathrm{addCharLevel}(\psi_{K,w})+1)+(52+3c_0(p))\bigr)\bigr)+3\bigr)+7\le k_\chi(p)$. An admissible character $\nu$ of the ideles of $K$ (`hνadm`) is given with $\mu=\nu\cdot(\chi_A\circ\mathrm{idelicNorm})$ (`hμν`), and archimedean data $u_{\mathbb R},a_{\mathbb R},u_{\mathbb C},k_{\mathbb C}$ realising the archimedean components of $\mu$ at the real and complex places of $K$ (`hcR`, `hcC`).
--
--   **Additive character and cubic induction form.** An additive character $\psi$ of the adeles of $\mathbb Q$ is given which is a global additive character (`hψ`: principal-invariant, continuous, nontrivial), with all local levels $0$ (`hlev`) and $\psi^{-1}=\psi_{\mathbb Q}$ (`hψQ`). Let $F$ be a `CubicInductionForm` for $K$, the pins `productionPinsOf ℚ` built from the class-representative Siegel set with parameters $(1/2,1,1/2,2)$, the level subgroups $\mathtt{levelOne}\sqcap\mathtt{finiteAdelicGL2Subgroup}$, the Hecke generators and the adelic box, the character $\psi$, and the twist $\nu$; thus $F$ carries a $\mathrm{GL}_3$ cusp form, its global, local and archimedean Whittaker functions, a central character, and a dual Whittaker function, with the automorphy, cuspidality, expansion, factorisation, sphericity, level-invariance, multiplicity-one and growth clauses of that structure. The hypotheses on $F$ are: `hF0`, that `F.form` $\neq 0$ and that at every $v$ unramified in $K$ with $\mathrm{addCharLevel}(\psi_v)=0$ one has $\mathtt{F.whittakerLoc}\,v\,1=1$ and `HasSphericalTorusValuesAt` for the induced coefficients of $\nu$; `hFc`, `hFw`, `hFdw`, continuity of `F.form`, `F.whittaker`, `F.dualWhittaker`; `hFg`, `hFdg`, gauge majorisation `IsGaugeMajorised3` of `F.whittaker` and `F.dualWhittaker`; `hBad`, that for every finite set $T$ of primes of $\mathbb Q$ and every $v\in T$ which is a bad place for $(K,\nu)$ (ramified in $K$, or $\nu$ twist-ramified above $v$) the local Whittaker function $\mathtt{F.whittakerLoc}\,v$ is right invariant under some open subgroup of $\mathrm{GL}_3$ over $\mathbb Q_v$ and generates an irreducible cyclic subspace (every nonzero member of its cyclic subspace generates it back); and `hcenu`, that `F.centralChar` is unitary.
--
--   **Auxiliary finite data.** A finite set $S'\supseteq\mathtt{SQ}$ (`hSS'`) is given with `hgood`: no prime outside $S'$ is a bad place for $(K,\mu)$. A family $\varpi$ of elements of the local valuation rings is given which, outside `SQ`, are nonzero (`hπ`) of valuation $\exp(-1)$ (`hϖ`), i.e. uniformisers.
--
--   **Local members at the level primes.** For $p\in\mathtt{SQ}$ a function $\mathrm{mP}_p$ on $\mathrm{GL}_3(\mathbb Q_p)$ is given lying in the cyclic subspace generated by $g\mapsto\chi_{A,p}(\det g)\,\mathtt{F.whittakerLoc}\,p\,g$ (`hmPmem`) and normalised by $\mathrm{mP}_p(1)=1$ (`hmP1`); `hW₃admM` is admissibility (the invariants of any open subgroup inside the cyclic subspace of $\mathrm{mP}_p$ are spanned by a finite set) and `hW₃irrM` irreducibility of that cyclic subspace. Integers $d_M(p)$ are given with `hπ₀levM`: the cyclic subspace of $\mathrm{mP}_p$ contains a nonzero vector whose $\chi_A\circ\det$-untwisting is right invariant under the elements of the maximal compact $\mathrm{GL}_3(\mathbb Z_p)$ congruent to $1$ modulo $\exp(-d_M(p))$. Numerical constraints `hkCM` ($6(b_{\mathbb Q}(p)+3d_M(p)+3)+7\le k_\chi(p)$) and `hΔM` ($6d_M(p)+18+\Delta_M(p)\le k_\chi(p)$, for a given family $\Delta_M$) are imposed. The hypothesis `hbumpAllM` produces bump vectors: for $p\in\mathtt{SQ}$, every admissible idele class character $\xi_A$ of $\mathbb Q$ unramified away from $p$ and with trivial archimedean component at the real places, and every $B\ge 2d_M(p)+6$ which is the conductor exponent of $\xi_{A,p}$, there is a vector $W_0$ in the cyclic subspace of $g\mapsto \xi_{A,p}(\det g)\chi_{A,p}(\det g)^{-1}\mathrm{mP}_p(g)$ which is right invariant under `congruenceK1` of level $3B+\Delta_M(p)$, right invariant under the image of the local level-$\top$ subgroup of $\mathrm{GL}_2$ under `iotaGL`, supported, along `iotaGL`, inside the product of the unipotent subgroup with that level subgroup, and normalised by $W_0(\mathtt{iotaGL}\,1)=1$.
--
--   **Local functional equations and vanishing.** A family $\lambda_M$ of complex numbers is given which is $1$ at places that are not bad for $(K,\mu)$ (`hlamM1`) and satisfies $\bigl(\prod_v \lambda_M(v)^2\bigr)\cdot\mathtt{lamSqArch}\,K=1$ (`hlamMProd`). The hypothesis `hlamMId` (summarised here) asserts, for $p\in\mathtt{SQ}$ and any sufficiently shallow local character $\eta$ at $p$ arising from an admissible global character whose base change is admissible, and all $g\in\mathrm{GL}_3(\mathbb Q_p)$, the existence of polynomials $Q_1,Q_2$ with $Q_2\neq0$, an integer $n$ and abscissae $\sigma_0,\sigma_1$ such that the local zeta integrals `localZeta30` and `localZetaDual31` of $\mathrm{mP}_p$ against $\eta$ converge in the indicated half-planes and satisfy the local functional equation with the same rational factor $Q_1/Q_2$ in $N(p)^{-s}$, the monomial $N(p)^{ns}$, and the root-number constant $\lambda_M(p)\cdot\prod_{w\mid p}\bigl((\eta_A\circ\mathrm{idelicNorm}\cdot\mu)_w(-1)\bigr)\cdot\prod_{w\mid p}\bigl(\mathtt{stdRootNumberAt}\,w\cdot (N(w)^{1/2-s})^{\mathtt{pinnedExp}\,w}\bigr)$. The hypothesis `hFE32lam` (summarised here) is the corresponding local Rankin–Selberg functional equation at a bad place $v\notin\mathtt{SQ}$ unramified in $K$ with $\psi_v=\psi_{\mathbb Q,v}^{-1}$: given a uniformiser, nonzero Satake parameters $a_1,a_2$, an unramified $\mathrm{GL}_2$ Whittaker function $W_2$ and its dual $W_2^\vee$ with the prescribed unipotent, level-$\top$, central and torus behaviour, Haar measures on $\mathrm{GL}_2(\mathbb Q_v)$ and on its unipotent subgroup, and any $W$ in the cyclic subspace of the $\chi_A\circ\det$-twist of $\mathtt{F.whittakerLoc}\,v$, there exist polynomials $p,q,p^\vee,q^\vee$ with $q,q^\vee\neq0$ and abscissae $\sigma_2,\sigma_3$ such that the two Rankin–Selberg integrands are integrable in the respective half-planes, the integrals `rsLocalIntegral` are the rational functions $p/q$ and $p^\vee/q^\vee$ of $N(v)^{-s}$, and these satisfy a functional equation whose factors are the induced Euler polynomials of $\mu$ and $\mu^{-1}$ evaluated at $a_i^{\pm1}N(v)^{\mp\cdots}$ and the square of $\lambda_M(v)\prod_{w\mid v}\mu_w(-1)\prod_{w\mid v}\mathtt{stdRootNumberAt}\,w(\mu_w)$. The hypothesis `hβM` states that, for $p\in\mathtt{SQ}$ with $b$ the exact exponent of $p$ in `Φ.level`, a uniformiser, any $g_3\in\mathrm{GL}_3(\mathbb Q_p)$, $k_0\in\mathrm{GL}_2(\mathbb Q_p)$, local character $\eta$ of conductor exponent at most $b$, and any Haar measure on $\mathrm{GL}_2(\mathbb Q_p)$, there is a finite set $T\subseteq\mathbb Z\times\mathbb Z$ of torus indices outside which both the corresponding torus-and-level integral of $\mathrm{mP}_p$ and its analogue for `dualWhittakerFn3` of $\mathrm{mP}_p(\cdot\,g_3)$ vanish.
--
--   **Central translate, finite Whittaker factors and archimedean sign.** An element $h_\mu$ of the finite adelic $\mathrm{GL}_2$ subgroup is given which, by `hhμf`, is the product over $p\in S'\setminus\mathtt{SQ}$ of the local embeddings of the scalar matrix $\varpi_p$ raised to the power $-\mathtt{inducedLevelAt}\,K\,\mu\,p$, where this exponent is $\sum_{\mathfrak P\mid p} f_{\mathfrak P}\cdot\mathrm{conductorExponentAt}\,\mathfrak P(\mu_{\mathfrak P})$. Functions $W_{A,\mathrm{par}}$ on $\mathrm{GL}_2(\mathbb R)$ and $W_{f,\mathrm{par}}$ on the finite adelic subgroup are given with `hWAf`: the first Whittaker coefficient of $\varphi_{\mathrm{par}}$ for the pins of $F$ and $\psi_{\mathbb Q}$ factorises as $W_{A,\mathrm{par}}(\mathtt{ratArchGL2}\,g)\cdot W_{f,\mathrm{par}}(\mathtt{finFactor}\,g)$; `hWfC`: $W_{f,\mathrm{par}}(g)=\mathtt{Cfin}\,1\,g$; and `hWf1`: $W_{f,\mathrm{par}}(1)\neq0$. The hypothesis `hV` states, for each parity and each $p\in\mathtt{SQ}$, that the local Whittaker space `localSpaceAt` of $\varphi_{\mathrm{par}}$ at $p$ is irreducible (every nonzero member generates it by right translates), admissible (the invariants of any open subgroup are finitely spanned) and smooth (every member is fixed by an open subgroup). An element $w_0\in\mathrm{GL}_2(\mathbb Q)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is fixed (`hw₀`) and the dual finite factor is defined by `hWfd`: $W^\vee_{f,\mathrm{par}}(g_f)=\|\det g_f\|\cdot W_{f,\mathrm{par}}(\mathtt{finFactor}(w_0\cdot{}^t g_f^{-1}))$. Finally $\varepsilon_\infty$ is fixed by `hεinf` as $\mathtt{archRootNumber}\,K$ for the constant parameter families $P$ and $P.\mathrm{baseChange}$ and the data $u_{\mathbb R},a_{\mathbb R},u_{\mathbb C},k_{\mathbb C}$, multiplied by $(-1)^{P.\mathrm{centralSign}}$ and by $(-1)^{\#\{\text{complex places of }K\}}$. The adelic $\mathrm{GL}_2$ is assumed second countable, and Haar measures $\mu_f$ on the finite adelic $\mathrm{GL}_2$ subgroup and $\mu_{N,f}$ on its unipotent subgroup `finUnipotent` are fixed.
--
--   **Conclusion.** Let $\mathrm{par}:\mathrm{InfinitePlace}(\mathbb Q)\to\mathbb Z/2$ be arbitrary and assume the archimedean non-vanishing hypothesis for it: with $\mathrm{GL}_2(\mathbb R)$ given its Borel structure, for every Haar measure $\mu_{N,\infty}$ on the unipotent subgroup of $\mathrm{GL}_2(\mathbb R)$ there exist $h_A\in\mathrm{GL}_2(\mathbb R)$, $h_{A,3}\in\mathrm{GL}_3$ of the infinite adeles of $\mathbb Q$ and $\sigma\in\mathbb R$ such that the archimedean Rankin–Selberg integral
--   $$s\mapsto \mathtt{rsArchIntegral}\ \mathtt{archMeasure}\ \mu_{N,\infty}\ s\ \bigl(M\mapsto |\det M|^{-1/2}W_{A,\mathrm{par}}(Mh_A)\bigr)\ \bigl(M\mapsto \mathtt{F.whittakerArch}(\mathtt{archComponent3}(\iota(\mathtt{archRealGLAt}\,M))\cdot h_{A,3})\bigr)$$
--   is complex differentiable on $\{\mathrm{Re}\,s>\sigma\}$ and nonzero at some point of that half-plane. Then there exist $n\in\mathbb N$, elements $k_0,\dots,k_{n-1}$ of $\mathrm{GL}_3$ of the adeles of $\mathbb Q$ each with trivial archimedean component and trivial component at every prime $v\notin\mathtt{SQ}$, coefficients $c_0,\dots,c_{n-1}\in\mathbb C$, an abscissa $\sigma_b\in\mathbb R$ and constants $\kappa,\kappa^\vee\in\mathbb C$ with $\kappa\neq0$, such that the following three assertions hold. Write $\mathcal C$ for the set of $g$ in the finite adelic $\mathrm{GL}_2$ subgroup whose component at each prime $p\notin\mathtt{SQ}$ lies in the product of the image of `unipotentGL2Hom` over $\mathbb Q_p$ with the local level-$\top$ subgroup, and $\mathbf 1_{\mathcal C}$ for the associated indicator truncation.
--
--   (i) For every $s'$ with $\mathrm{Re}\,s'>\sigma_b$,
--   $$\sum_{i} c_i\cdot \mathtt{rsFinIntegral}\ \mu_f\ \mu_{N,f}\ s'\ \Bigl(\mathbf 1_{\mathcal C}\bigl(g\mapsto W_{f,\mathrm{par}}(\mathtt{finFactor}\,g)\bigr)\Bigr)\ \Bigl(\mathbf 1_{\mathcal C}\bigl(g\mapsto \prod_v \chi_{A,v}(\det)\,\mathtt{F.whittakerLoc}\,v\ \text{at}\ \mathtt{componentAt3}\,v\,(\iota(\mathtt{finFactor}\,g)\cdot k_i)\bigr)\Bigr)=\kappa,$$
--   the inner product over all finite places being the multipliable product of the $\chi_A\circ\det$-twisted local Whittaker functions of $F$; in particular this sum is constant in $s'$ on the half-plane.
--
--   (ii) For every $s'$ with $\mathrm{Re}\,s'>\sigma_b$, the same sum with the first function replaced by $\mathbf 1_{\mathcal C}\bigl(g\mapsto W^\vee_{f,\mathrm{par}}(\mathtt{finFactor}\,g\cdot h_\mu)\bigr)$ and the second by $\mathbf 1_{\mathcal C}$ applied to $g\mapsto\prod_v \mathtt{dualWhittakerFn3}$ of the $\chi_A\circ\det$-twisted $\mathtt{F.whittakerLoc}\,v$ evaluated at $\mathtt{componentAt3}\,v\,(\iota(\mathtt{finFactor}\,g\cdot h_\mu)\cdot \mathtt{transposeInv3}\,k_i)$ equals
--   $$\kappa^\vee\cdot\bigl(\mathtt{finiteConductor}\,K\,\mu\,\mathtt{SK}\bigr)^{1/2}\cdot\Bigl(\prod_{w\in \mathtt{SK}}\mathtt{stdRootNumberAt}\,w\bigl((\omega\mu)_w\bigr)\,\mathtt{stdRootNumberAt}\,w(\mu_w)\,\bigl(N(w)^{1/2-t}\bigr)^{-(\mathtt{pinnedExp}(\omega\mu,w)+\mathtt{pinnedExp}(\mu,w))}\Bigr)\Big|_{t=s'+1/2},$$
--   where `finiteConductor` is the multipliable product of $N(\mathfrak P)^{2\,\mathtt{pinnedExp}(\mu,\mathfrak P)}$ over the primes of $K$ outside `SK`, and $\mathtt{pinnedExp}$ is the local conductor exponent plus the level of $\psi_{K,\cdot}$.
--
--   (iii) $\kappa^\vee\cdot\varepsilon_\infty=\mathtt{pinnedRootNumber}\,K\,(\mathtt{formalBaseChange ℚ}\,K\,\Phi)\,\mu\,\mathtt{SK}\,(\mathtt{archOfParamR}\,K\,P)\,(\mathtt{archOfParamC}\,K\,P)\,u_{\mathbb R}\,a_{\mathbb R}\,u_{\mathbb C}\,k_{\mathbb C}\cdot\kappa$, the right-hand factor being the product of the archimedean root number for those constant parameter families with the finite root number of the formal base change of $\Phi$ relative to $\mu$ and `SK`.
--
--   This is the finite-place leaf of the Rankin–Selberg construction for $\Phi$ against the automorphic induction of $\mu$ from the cubic field $K$: a finite linear combination of $\mathrm{GL}_3$-translated finite Rankin–Selberg integrals, the translates being supported at the level primes, is constant in $s'$ and its dual counterpart is the same constant times the expected conductor and root-number monomial, with the two constants linked by the pinned root number. It is used by the assembly of the entire pair of completed $L$-functions, [`LanglandsTunnell.RankinSelberg.exists_entire_boundedOnStrips_eq_archFactor_mul_lFun_rsDatum_of_le_conductorExponentAt_of_centralInduced_of_localSpaceAt_of_normPin_archTrivial`](thm.html#LanglandsTunnell.RankinSelberg.exists_entire_boundedOnStrips_eq_archFactor_mul_lFun_rsDatum_of_le_conductorExponentAt_of_centralInduced_of_localSpaceAt_of_normPin_archTrivial), which feeds the converse-theorem input of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_gl3Translates_sum_rsFinIntegral_cells_eq_const_and_dual_eq_rootNumberMonomial_of_finWhittaker_one_ne_zero_of_localSpaceAt_of_member_of_fe32_normPin_twisted_offSQ_archPsi_bump_levelShift_global.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_gl3Translates_sum_rsFinIntegral_cells_eq_const_and_dual_eq_rootNumberMonomial_of_finWhittaker_one_ne_zero_of_localSpaceAt_of_member_of_fe32_normPin_twisted_offSQ_archPsi_bump_levelShift_global
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

    (hcenu : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖((F.centralChar z : ℂˣ) : ℂ)‖ = 1)

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

    (dM : ↥SQ → ℕ)
    (hπ₀levM : ∀ p : ↥SQ, ∃ W' ∈ gl3CyclicSubspace (mP p), W' ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)),
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) i j) ≤ WithZero.exp (-(dM p : ℤ))) →
        ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)),
          ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
            ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)
    (hkCM : ∀ p : ↥SQ, 6 * (bQ (p : HeightOneSpectrum (𝓞 ℚ)) + 3 * dM p + 3) + 7 ≤ kχ (p : HeightOneSpectrum (𝓞 ℚ)))

    (ΔM : ↥SQ → ℕ) (hΔM : ∀ p : ↥SQ, 6 * dM p + 18 + ΔM p ≤ kχ (p : HeightOneSpectrum (𝓞 ℚ)))

    (hbumpAllM : ∀ p : ↥SQ, ∀ (ξA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ξA →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ (p : HeightOneSpectrum (𝓞 ℚ)) → NumberField.TateGlobal.IsUnramifiedCharAt ξA v) →
      (∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ ξA v 0 0) →
      ∀ B : ℕ, 2 * dM p + 6 ≤ B →
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))
        (NumberField.TateGlobal.localChar ξA (p : HeightOneSpectrum (𝓞 ℚ))) B →
      ∃ W₀ ∈ gl3CyclicSubspace (fun g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) =>
          ((NumberField.TateGlobal.localChar ξA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ *
              mP p g),
        (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (3 * B + ΔM p), ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)),
          W₀ (g * k) = W₀ g) ∧
        (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ⊤,
          ∀ h : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) ∧
        (∀ h : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
          ∃ x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ,
            ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ⊤, h = unipotentGL2 x * k) ∧
        W₀ (iotaGL 1) = 1)

    (lamM : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (hlamM1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → lamM v = 1)
    (hlamMProd : (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), lamM v ^ 2) * lamSqArch K = 1)
    (hlamMId : ∀ p : ↥SQ,
    ∀ b : ℕ,
            (∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K (p : HeightOneSpectrum (𝓞 ℚ)),
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ (η : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
          LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) η cη → cη ≤ b →
          ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
            NumberField.TateGlobal.localChar ηA (p : HeightOneSpectrum (𝓞 ℚ)) = η →
            LanglandsTunnell.Converse.IsAdmissibleTwist K
              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
            ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)),
              letI := LanglandsTunnell.TateLocal.localBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
              ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                IsLocalZeta30ConvergentAbove (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))))
                  (mP p) η g σ₀ ∧
                (∀ s : ℂ, σ₀ < s.re →
                  localZeta30 (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))))) (mP p) η s g *
                    Q₂.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                IsLocalZeta31ConvergentAbove (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))) (dualWhittakerFn3 (mP p)) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                (∀ s : ℂ, σ₁ < (1 - s).re →
                  localZetaDual31 (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))
                    (mP p) η (1 - s) g * Q₂.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ ((n : ℂ) * s) *
                    (lamM (p : HeightOneSpectrum (𝓞 ℚ)) *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K (p : HeightOneSpectrum (𝓞 ℚ)),
                        ((NumberField.TateGlobal.localChar
                          (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K (p : HeightOneSpectrum (𝓞 ℚ)),
                        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                            (NumberField.TateGlobal.localChar
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                            (LanglandsTunnell.Converse.pinnedExp K
                                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))))

    (hFE32lam : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → v ∉ SQ → ¬ IsRamifiedIn K v →
          psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ →
          ∀ {ϖ : v.adicCompletionIntegers ℚ}
            (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0),
            Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) →
            ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
            (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
            (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
              W₂ (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
            (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
              k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
            (hW₂1 : W₂ 1 = 1)
            (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
              W₂ (g * UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
                a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
            (hW₂T : ∀ m : ℤ, W₂ (UnramifiedWhittaker.diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
              UnramifiedWhittaker.torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m)
            (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
            (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
              W₂d (UnramifiedWhittaker.unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
            (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
              k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
            (hW₂d1 : W₂d 1 = 1)
            (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
              W₂d (g * UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
                (Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂) * W₂d g)
            (hW₂dT : ∀ m : ℤ, W₂d (UnramifiedWhittaker.diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
              UnramifiedWhittaker.torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * (a₁ + a₂) / (a₁ * a₂))
                ((Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂)) m),
            letI := localGLBorel ℚ v
            haveI := borelSpace_localGLBorel ℚ v
            ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
              (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
            ∀ W ∈ gl3CyclicSubspace
              (fun g : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc v g),
            ∃ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 ∧ qd ≠ 0 ∧
              (∀ s : ℂ, σ₂ < s.re →
                Integrable
                  (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                    (W (iotaGL g) * W₂ g) *
                      ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                          v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
                  (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
              (∀ s : ℂ, σ₃ < (1 - s).re →
                Integrable
                  (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                    (dualWhittakerFn3 W (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                          (-(inducedLevelAt K μ v : ℤ)))) * W₂d g) *
                      ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                          v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
                  (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
              (∀ s : ℂ, σ₂ < s.re →
                RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
                    (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                      (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
                    s (fun g => W (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
                  p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
              (∀ s : ℂ, σ₃ < (1 - s).re →
                RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
                    (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                      (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
                    (1 - s) (fun g => dualWhittakerFn3 W (iotaGL g * iotaGL
                        (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                        (-(inducedLevelAt K μ v : ℤ))))) W₂d *
                    qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
                  pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) ∧
              (∀ s : ℂ,
                pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
                    (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval (a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                        s))) *
                    (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval (a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                        s))) =
                  p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))
                      *
                    (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                        2))) *
                    (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                        2))) *
                    (lamM v * ((∏ᶠ w ∈ primeFibre ℚ K v, ((localChar μ w (-1) : ℂˣ) : ℂ)) *
                      ∏ᶠ w ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K w (localChar μ w))) ^ 2))

    (hβM : ∀ p : ↥SQ, ∀ b : ℕ, ((p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ b ∣ Φ.level ∧ ¬ (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ (b + 1) ∣ Φ.level) →
      ∀ (ϖp : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ)
        (hπp : algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp ≠ 0),
        Valued.v (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) = WithZero.exp (-1 : ℤ) →
      ∀ (g₃ : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))) (k₀ : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (η : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ →* ℂˣ)
      (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) η c → c ≤ b →
      letI := LanglandsTunnell.TateLocal.localBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      letI := localGLBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      haveI := borelSpace_localGLBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      ∀ (μ₂ : Measure (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ | Valued.v (u : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ (b)) :
                    Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))),
                  (mP p) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))))) = 0 ∧
          (∫ u in {u : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ | Valued.v (u : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ (b)) :
                    Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => (mP p) (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))))) = 0)
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

    (εinf : ℂ)
    (hεinf : εinf = (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val *
        (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card))

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : MeasureTheory.Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure] :

    ∀ (par : InfinitePlace ℚ → ZMod 2),
      (letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
      ∀ (μNA : Measure RSCarrier.realUnipotent) [μNA.IsHaarMeasure],
        ∃ (hA : GL (Fin 2) ℝ) (hA3 : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : ℝ),
          DifferentiableOn ℂ
              (fun s : ℂ => RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s
                (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA par (M * hA)))
                (fun M : GL (Fin 2) ℝ => F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)))
              {s : ℂ | σ < s.re} ∧
          ∃ s : ℂ, σ < s.re ∧
            RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s
                (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA par (M * hA)))
                (fun M : GL (Fin 2) ℝ => F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)) ≠ 0) →
    ∃ (n : ℕ) (k : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ)
        (_ : ∀ i : Fin n, archComponent3 (𝓞 ℚ) ℚ (k i) = 1 ∧
          ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v (k i) = 1)
        (coef : Fin n → ℂ) (σb : ℝ) (κ κd : ℂ),
        κ ≠ 0 ∧

        (∀ (s' : ℂ), σb < s'.re →
          ∑ i, coef i *
            RSCarrier.rsFinIntegral μf μNFin s'
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wf par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v,
                  (fun g : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc v g)
                  (componentAt3 (𝓞 ℚ) ℚ v
                    (iota (𝓞 ℚ) ℚ ((RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) : finiteAdelicGL2Subgroup ℚ) :
                      AdelicGL2 (𝓞 ℚ) ℚ) * k i)))) = κ) ∧

        (∀ (s' : ℂ), σb < s'.re →
          ∑ i, coef i *
            RSCarrier.rsFinIntegral μf μNFin s'
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wfd par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)))
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v, dualWhittakerFn3
                  (fun g : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc v g)
                  (componentAt3 (𝓞 ℚ) ℚ v
                    (iota (𝓞 ℚ) ℚ ((RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf : finiteAdelicGL2Subgroup ℚ) :
                      AdelicGL2 (𝓞 ℚ) ℚ) * transposeInv3 (k i))))) =
            κd * (((finiteConductor K μ SK) : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * (fun t : ℂ => ∏ w : ↥SK,
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
        LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
        (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
        (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) (s' + 1 / 2)) ∧

        κd * εinf = (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P) uR aR uC kC) * κ := by sorry
