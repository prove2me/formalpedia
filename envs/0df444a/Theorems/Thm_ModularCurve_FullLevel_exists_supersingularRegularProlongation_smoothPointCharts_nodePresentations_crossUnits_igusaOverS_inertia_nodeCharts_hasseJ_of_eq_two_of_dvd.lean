-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/7588c72f-9528-5786-a841-36e4553c3de7
-- title:
--   Supersingular prolongation, node package and Drinfeld inertia at q=2
-- statement:
--   Throughout, $q$ is a prime with $q=2$, $M'$ a nonzero natural number not divisible by $q$, and $\ell$ a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense of `LiesOverPrime`, i.e. $(q:\overline{\mathbb{Q}})$ is a nonunit of $A$; write $\kappa := \mathrm{ResidueField}\,A$. The finite set $W$ of places of $\mathcal{M} := \mathrm{modularFunctionFieldC}\,\kappa\,M' = \kappa(j, j_{M'})$ over $\kappa$ is required by `hW` to consist exactly of the members of `ssPlaces q M' κ`, that is of those places $w$ which are rational (the structure map $\kappa \to w.\mathrm{ResidueField}$ is surjective), satisfy `IsAffineGeomPlace`, and have $w.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M')$ in `ssJSet q κ`; and $s \in W$ is a chosen such place. Write $F_0 := \mathrm{modularFunctionFieldBar}\,M'$ for the $\overline{\mathbb{Q}}$-base change inside $\overline{\mathbb{Q}}((t))$ of the full level-$M'$ modular function field, and $F := \mathrm{fieldBar}\,q\,M' = xH\mathrm{FunctionFieldBar}(q^2M', \mathrm{levelH}\,q\,M')$, the corresponding base change of the function field of the $X_H$ of level $q^2M'$ whose level subgroup $\mathrm{levelH}\,q\,M'$ is the kernel of the reduction $(\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/q)^{\times}$, i.e. the units congruent to $1$ modulo $q$; the hypothesis `hle` is the inclusion $F_0 \le F$. Next, $R_0$ is a `ConstantReduction` of $A$ from $F_0$ to $\mathcal{M}$ (a valuation subring $R_0.\mathrm{integers}$ of $F_0$ together with a surjective residue map onto $\mathcal{M}$ whose kernel is the maximal ideal, extending $A \to \kappa$ on constants, with a place map preserving degrees and orders), and `hR₀` requires $R_0$ to be coefficientwise reduction: for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}((t))$ lies in $F_0$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction of $y$. Finally $\pi \in A$ satisfies $\pi^{q^2-1} = q$.
--
--   For brevity, $j$ denotes the element $\mathrm{coeffEmb}\,\overline{\mathbb{Q}}\,jq$ of $F_0$ (and also its image in $F$ under the inclusion `hle`); an element $f$ of $F_0$ is called $j$-integral if $0 \le P.\mathrm{ord}(f)$ for every place $P$ of $F_0$ over $\overline{\mathbb{Q}}$ with $0 \le P.\mathrm{ord}(j)$. A place $P$ of $F$ over $\overline{\mathbb{Q}}$ is said to lie over $s$ if for every $f \in R_0.\mathrm{integers}$ which is $j$-integral and whose $R_0$-residue lies in the valuation subring of $s$, and for every $a \in A$ with $\mathrm{residue}_A(a) = s.\mathrm{evalAt}(R_0.\mathrm{residue}\,f)$, the difference $P.\mathrm{evalAt}(f) - a$ lies in $A$ and in the maximal ideal of $A$.
--
--   The assertion is the existence of a field $FSS$ with a $\kappa$-algebra structure and a `RegularProlongation` $R$ of $A$ from $F$ to $FSS$ (a valuation subring $R.\mathrm{integers}$ of $F$ with a surjective residue map onto $FSS$ whose kernel is the maximal ideal, meeting $\overline{\mathbb{Q}}$ in $A$ and inducing $A \to \kappa$ there, and such that every nonzero element of $F$ can be scaled by a constant into $R.\mathrm{integers}$ with nonzero residue) such that the following hold.
--
--   First, $FSS$ contains an element transcendental over $\kappa$. Secondly, $R$ specialises $R_0$ at $s$: for every $f \in R_0.\mathrm{integers}$ which is $j$-integral and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $F$ lies in $R.\mathrm{integers}$ and its $R$-residue is the image under $\kappa \to FSS$ of $s.\mathrm{evalAt}(R_0.\mathrm{residue}\,f)$. Thirdly, $R.\mathrm{integers}$ is invariant under the level automorphisms: for every $\zeta \in \mathrm{Idx}\,q$ (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in \Gamma_0(M')$, the comap of $R.\mathrm{integers}$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ is $R.\mathrm{integers}$.
--
--   Furthermore there exist a finite set $N$ of places of $FSS$ over $\kappa$, subrings $Sx\,Q \subseteq F$, ring maps $\varphi x\,Q : A[X] \to Sx\,Q$ and $\chi_0x\,Q : Sx\,Q \to \kappa$, and sets $Dx\,Q$ of places of $F$ over $\overline{\mathbb{Q}}$, indexed by the places $Q$ of $FSS$, with the following properties.
--
--   (i) $|N| = q+1$.
--
--   (ii) For every $Q \notin N$: the image of $A$ in $F$ lies in $Sx\,Q$; $\varphi x\,Q$ is formally smooth and formally unramified; $\varphi x\,Q(C\,a)$ is the image of $a$ in $F$ for $a \in A$; $\chi_0x\,Q(\varphi x\,Q(C\,a)) = \mathrm{residue}_A(a)$; $\chi_0x\,Q(\varphi x\,Q(X)) = 0$; for every $c \in A$ with $\mathrm{residue}_A(c) = 0$ there is a unique ring map $\chi : Sx\,Q \to A$ with $\chi(\varphi x\,Q(C\,a)) = a$ for all $a$, $\mathrm{residue}_A \circ \chi = \chi_0x\,Q$ and $\chi(\varphi x\,Q(X)) = c$; every $f \in Sx\,Q$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$, and the residue there equals the image of $\chi_0x\,Q(f)$ under $\kappa \to Q.\mathrm{ResidueField}$; $\varphi x\,Q(X)$ lies in $R.\mathrm{integers}$ and the $Q$-order of its $R$-residue is $1$; $Dx\,Q$ consists precisely of the rational places $P$ such that every $f \in Sx\,Q$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f) \in A$, and such that for every $f \in Sx\,Q$ the $A$-valuation of $P.\mathrm{evalAt}(f)$ is $< 1$ exactly when $\chi_0x\,Q(f) = 0$; every ring map $\chi : Sx\,Q \to A$ which is the identity on the constants $\varphi x\,Q(C\,a)$ and reduces to $\chi_0x\,Q$ comes from a unique $P \in Dx\,Q$ with $P.\mathrm{evalAt}(f) = \chi(f)$ for all $f$; for $P \in Dx\,Q$, an element $f \in F$ lies in the valuation subring of $P$ exactly when $f\,h = g$ for some $g, h \in Sx\,Q$ with $P.\mathrm{evalAt}(h) \neq 0$; every nonzero $f \in F$ with $P.\mathrm{ord}(f) = 0$ for all $P \in Dx\,Q$ satisfies $c\,f = u$ for some nonzero constant $c \in \overline{\mathbb{Q}}$ and some unit $u$ of $Sx\,Q$; and every $f \in R.\mathrm{integers}$ lying in the valuation subring of every $P \in Dx\,Q$ lies in $Sx\,Q$.
--
--   (iii) The discs are pairwise disjoint: if $Q, Q' \notin N$ and some $P$ lies in both $Dx\,Q$ and $Dx\,Q'$, then $Q = Q'$.
--
--   (iv) For $Q \notin N$ and $P \in Dx\,Q$ one has $0 \le P.\mathrm{ord}(j)$.
--
--   (v) Level equivariance of $N$ and of the discs: for every $\tau$ in the subgroup of $\mathrm{Aut}_{\overline{\mathbb{Q}}}(F)$ generated by the automorphisms $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma \in \Gamma_0(M')$, and any witness that $\tau$ preserves $R.\mathrm{integers}$, the induced residue automorphism $R.\mathrm{resAut}\,\tau$ preserves $N$ setwise, and for $Q \notin N$ one has $\mathrm{smulDisc}\,\tau\,(Dx\,Q) = Dx(R.\mathrm{resAut}\,\tau \cdot Q)$.
--
--   (vi) Drinfeld identification: for every $\mathbb{F}_{q^2}$-algebra structure on $\kappa$ for which $\mathrm{CoordRing}\,q\,\kappa$ (the quotient of $\kappa[x_0,x_1]$ by the Drinfeld relation) is a domain, and every $\zeta$, there exist a subgroup $C_s$ of $\mu_{q+1}(\mathbb{F}_{q^2})$ and a $\kappa$-algebra isomorphism $e$ of $FSS$ with the fixed field $\mathrm{quotField}\,q\,\kappa\,C_s$ inside the Drinfeld function field, such that $\#C_s = \mathrm{placeWidthChar}\,q\,M'\,s$ (that is, $\mathrm{jWidthChar}\,q$ of $s.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M')$, which for $q=2$ is $12$ at $j=0$ and $1$ otherwise, divided by $\mathrm{placeRamificationJ}\,M'\,s$), and such that for $\gamma \in \Gamma_0(M')$ with $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ preserving $R.\mathrm{integers}$ and with $(\mathrm{redQ}\,q\,\gamma, 1) \in \mathrm{hSubgroup}\,q$, the map $e$ intertwines the residue automorphism of $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ with the action of $(\mathrm{redQ}\,q\,\gamma,1)$ through $\mathrm{hFunctionFieldAction}$.
--
--   (vii) Transport along semilinear automorphisms: let $g$ be a semilinear automorphism of $F$ over $\overline{\mathbb{Q}}$ (a pair consisting of an automorphism of $F$ and one of $\overline{\mathbb{Q}}$ compatible with the structure map) whose base automorphism preserves $A$, which preserves $R.\mathrm{integers}$ and fixes $j$; let $\psi$ be a ring automorphism of $\kappa$ compatible with the base automorphism of $g$ through $\mathrm{residue}_A$, and $\varphi$ a ring automorphism of $FSS$ with $R.\mathrm{residue}(g \cdot f) = \varphi(R.\mathrm{residue}\,f)$ for $f \in R.\mathrm{integers}$. Then for all places $Q, Q'$ of $FSS$ with $Q \notin N$ and $Q'$ the transport of $Q$ along $\varphi$ (i.e. $y$ lies in the valuation subring of $Q'$ exactly when $\varphi^{-1}(y)$ lies in that of $Q$), one has $Q' \notin N$, $f \in Sx\,Q \iff g \cdot f \in Sx\,Q'$, with $\chi_0x\,Q'(g \cdot f) = \psi(\chi_0x\,Q\,f)$, and $P \in Dx\,Q \iff g \cdot P \in Dx\,Q'$ for all places $P$ of $F$ over $\overline{\mathbb{Q}}$.
--
--   (viii) The level group acts transitively on $N$: for all $x, x' \in N$ there are $\zeta$ and $\gamma \in \Gamma_0(M')$ whose level automorphism preserves $R.\mathrm{integers}$ and whose residue automorphism carries $x$ to $x'$. (ix) No place outside $N$ is fixed by all of them: for each $Q \notin N$ there are $\zeta$ and $\gamma \in \Gamma_0(M')$, with the corresponding preservation of $R.\mathrm{integers}$, whose residue automorphism moves $Q$.
--
--   (x) Generation: there are finitely many elements $g_1,\dots,g_n$ of $R.\mathrm{integers}$ such that each $g_i$ lies in the valuation subring of every $P \in Dx\,Q$ for $Q \notin N$ with $P.\mathrm{evalAt}(g_i) \in A$, and such that every $f \in FSS$ lying in the valuation subring of every $Q \notin N$ lies in the $\kappa$-subalgebra of $FSS$ generated by the residues $R.\mathrm{residue}(g_i)$.
--
--   (xi) Annuli at the ends. There is an assignment $An$ of an `Annulus` of $A$ in $F$ to each place of $FSS$ — a set of places $(An\,x).\mathrm{dom}$, a parameter $(An\,x).\mathrm{param}$ and a modulus in the maximal ideal of $A$, subject to the axioms of `Annulus`: each place of the domain is rational, the parameter is integral there with evaluation a nonzero element of the maximal ideal dividing the modulus; each admissible value of the parameter is attained by a unique place of the domain; the parameter minus its value has order $1$; and a unit principle holds — such that: for each $x \in N$ the parameter lies in $R.\mathrm{integers}$ with $x$-order of its residue equal to $1$, and for every $f \in R.\mathrm{integers}$ with nonzero residue and $P.\mathrm{ord}(f) = 0$ throughout the domain, the product of $P.\mathrm{evalAt}(f)$ with $P.\mathrm{evalAt}(\mathrm{param})^{-x.\mathrm{ord}(R.\mathrm{residue}\,f)}$ is a unit of $A$ at every $P$ of the domain; the modulus is nonzero; the domain meets no $Dx\,Q$ with $Q \notin N$; and every place of the domain lies over $s$. Distinct $x, x' \in N$ have disjoint annulus domains; the level group permutes the annuli, $\mathrm{smulDisc}\,\tau\,((An\,x).\mathrm{dom}) = (An(R.\mathrm{resAut}\,\tau \cdot x)).\mathrm{dom}$ for $\tau$ as in (v) and $x \in N$; the discs and annuli cover: every rational place $P$ of $F$ over $\overline{\mathbb{Q}}$ lying over $s$ belongs to some $Dx\,Q$ with $Q \notin N$ or to some $(An\,x).\mathrm{dom}$ with $x \in N$; and the annuli are separated by functions: for $x \neq x'$ in $N$ there is $g \in R.\mathrm{integers}$ with nonzero residue, nonzero $x$-order of that residue, $P.\mathrm{ord}(g) = 0$ on $(An\,x).\mathrm{dom}$, and $g$ integral with unit value at every place of $(An\,x').\mathrm{dom}$.
--
--   (xii) Node presentations. Together with the annuli there exist: fields $FIx\,x$ over $\kappa$, regular prolongations $Rx\,x$ of $A$ from $F$ to $FIx\,x$ and places $bx\,x$ of $FIx\,x$ over $\kappa$, indexed by places $x$ of $FSS$; an index type $\Lambda$ with subrings $C'(l) \subseteq \overline{\mathbb{Q}}$ all contained in $A$, each a domain and a discrete valuation ring, with elements $\varpi'(l)$ and a base index $l_0$; complete discrete valuation rings $Wc(l)$ with elements $\pi W(l)$, natural numbers $E(l)$ and $E_0$; sets $S(nd)$ of places of $F$, subrings $\mathcal{N}(nd)$ and $\mathcal{N}_0(nd,l)$ of $F$, the latter local and Noetherian, and elements $cx(nd), cy(nd), cu(nd)$ of $F$; subject to: $\mathrm{residue}_A(d) = 0$ for $d \in C'(l)$ exactly when $d \in \varpi'(l)C'(l)$; $C'(l_0) \subseteq C'(l)$ for all $l$; $\varpi'(l_0) \neq 0$; every element of $A$ is algebraic over $C'(l_0)$; $\pi W(l)$ irreducible and $E(l) \ge 1$; invariance of $\varpi'(l_0)$ under every $\tau$ in the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\,\mathbb{Q}$ with $A.\mathrm{tameCharacter}\,\pi\,\tau = 1$; and the existence of $w \ge 1$ and a unit $v$ of $A$ with $\varpi'(l_0)^{E_0} = v\,\pi^{w}$ in $A$.
--
--   For each $nd \in N$ the following hold: $bx(nd)$, $nd$ and all places of $S(nd)$ are rational; $\mathcal{N}(nd)$ consists of the elements of $Rx(nd).\mathrm{integers} \cap R.\mathrm{integers}$ integral at all places of $S(nd)$, and such elements have values in $A$ at those places; the crossing relation $cx(nd)\,cy(nd) = \varpi'(l_0)^{E_0}\,cu(nd)$ holds in $F$; $cx(nd)$ has $Rx(nd)$-residue $0$ and $R$-residue of $nd$-order $1$, while $cy(nd)$ has $R$-residue $0$ and $Rx(nd)$-residue of $bx(nd)$-order $1$; for $\tau$ in the inertia subgroup with trivial tame character, the semilinear automorphism $\mathrm{arithmeticGalois}$ attached to $\tau$ on $F$ preserves $S(nd)$ and fixes $cx(nd)$ and $cy(nd)$; every element of $F$ is a quotient of two elements of some $\mathcal{N}_0(nd,l)$, and is, after multiplication by a nonzero element of $\mathcal{N}_0(nd,l_0)$, a finite $\overline{\mathbb{Q}}$-linear combination of elements of $\mathcal{N}_0(nd,l_0)$. For each $l$: $\mathcal{N}_0(nd,l_0) \subseteq \mathcal{N}_0(nd,l) \subseteq \mathcal{N}(nd)$; $S(nd)$ is exactly the set of places $P$ integral on $\mathcal{N}_0(nd,l)$ which send nonunits of $\mathcal{N}_0(nd,l)$ into the maximal ideal of $A$; the constants from $C'(l)$ lie in $\mathcal{N}_0(nd,l)$, and every element of $\mathcal{N}_0(nd,l)$ differs from such a constant by a nonunit; $C'(l)$-linearly independent families of constants remain independent against $\mathcal{N}_0(nd,l)$, in the sense that a vanishing combination $\sum c_i a_i = 0$ forces all $a_i = 0$; there is a subring $Bx \subseteq \mathcal{N}_0(nd,l)$ containing $cx(nd), cy(nd), cu(nd)$, of which $\mathcal{N}_0(nd,l)$ is the localisation (every element is $g/h$ with $g,h \in Bx$ and $h$ a unit of $\mathcal{N}_0(nd,l)$), and $Bx$ is generated as a subring by the constants from $C'(l)$ together with a finite set; $cx(nd), cy(nd) \in \mathcal{N}_0(nd,l)$ and $cu(nd)$ is a unit there; and there are a ring map $\sigma$ from $Wc(l)$ to the adic completion of $\mathcal{N}_0(nd,l)$ at its maximal ideal and a ring isomorphism $\iota$ of that completion with the crossing model $\mathrm{UVCrossingModel}(Wc(l), \pi W(l)^{E(l)}) = Wc(l)[[U,V]]/(UV - \pi W(l)^{E(l)})$, such that $\sigma(\pi W(l))$ is the image of the constant $\varpi'(l)$, $\iota \circ \sigma$ is the constant map, every constant from $C'(l)$ lies in the image of $\sigma$, and the orders are read off in the model: if $f \in \mathcal{N}_0(nd,l)$ has nonzero $Rx(nd)$-residue of $bx(nd)$-order $n$ then $\iota(f) \equiv \gamma V^{n}$ modulo the ideal generated by the constant $\pi W(l)$ and $U$ for some unit $\gamma$, and symmetrically with nonzero $R$-residue of $nd$-order $n$, $\iota(f) \equiv \gamma U^{n}$ modulo the ideal generated by the constant $\pi W(l)$ and $V$.
--
--   The same package contains a Hasse-invariant clause: $\mathrm{jqNModC}\,\overline{\mathbb{Q}}\,q$ lies in $F$, and there is $a_0 \in A$ with $\mathrm{jqNModC}\,\overline{\mathbb{Q}}\,q - a_0$ in $R.\mathrm{integers}$ of residue $0$ and with $\mathrm{residue}_A(a_0)^q = s.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M')$, together with a constant $c'$ such that $c'(\mathrm{jqNModC}\,\overline{\mathbb{Q}}\,q - a_0)$ lies in $R.\mathrm{integers}$ with nonzero residue, and such that for every $nd \in N$ the element $\mathrm{jqNModC}\,\overline{\mathbb{Q}}\,q - a_0$ lies in $Rx(nd).\mathrm{integers}$ with nonzero residue and $nd.\mathrm{ord}$ of the $R$-residue of $c'(\mathrm{jqNModC}\,\overline{\mathbb{Q}}\,q - a_0)$ equals minus the $bx(nd)$-order of that $Rx(nd)$-residue. Moreover: distinct $nd, nd' \in N$ have disjoint $S$-sets; every place of $S(nd)$ lies over $s$; for each $\zeta'$ and $\gamma \in \Gamma_0(M')$ there is a map $\tau N$ on places of $FSS$ preserving $N$ with $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma \cdot P \in S(nd) \iff P \in S(\tau N(nd))$ and with the comap of $Rx(nd).\mathrm{integers}$ along that level automorphism equal to $Rx(\tau N(nd)).\mathrm{integers}$; for $\tau$ as in (v) and $nd \in N$, $R.\mathrm{resAut}\,\tau \cdot nd \in N$ and $\mathrm{smulDisc}\,\tau\,(S(nd)) = S(R.\mathrm{resAut}\,\tau \cdot nd)$; $S(nd) = (An\,nd).\mathrm{dom}$; the image in $F$ of $R_0.\mathrm{integers}$ lies in $Rx(nd).\mathrm{integers}$; and there is a ring map $j_{nd} : \mathcal{M} \to FIx(nd)$ with $Rx(nd).\mathrm{residue}$ of the image of $f \in R_0.\mathrm{integers}$ equal to $j_{nd}(R_0.\mathrm{residue}\,f)$, and with $g$ in the valuation subring of $s$ exactly when $j_{nd}(g)$ is in that of $bx(nd)$.
--
--   (xiii) Drinfeld identification with inertia. For every ring map $\iota : \mathbb{F}_{q^2} \to \kappa$, taken as the algebra structure, such that $\mathrm{CoordRing}\,q\,\kappa$ is a domain, there is a subgroup $C_s$ of $\mu_{q+1}(\mathbb{F}_{q^2})$ with $\#C_s = \mathrm{placeWidthChar}\,q\,M'\,s$, and for every $\zeta$ there are an exponent $\eta \in \{1, q\}$ and a $\kappa$-algebra isomorphism $e$ of $FSS$ with $\mathrm{quotField}\,q\,\kappa\,C_s$ such that the $\Gamma_0(M')$-equivariance of (vi) holds for $e$, and, in addition, for every $\tau$ in $A.\mathrm{inertiaSubgroupIn}\,\mathbb{Q}$ and every $\alpha \in \mathbb{F}_{q^2}^{\times}$ with $\iota(\alpha) = A.\mathrm{tameCharacter}\,\pi\,\tau$, the semilinear automorphism $g$ of $F$ attached to $\tau$ by $\mathrm{arithmeticGalois}$ preserves $R.\mathrm{integers}$, and for every ring automorphism $\varphi$ of $FSS$ with $R.\mathrm{residue}(g \cdot f) = \varphi(R.\mathrm{residue}\,f)$, every $d \in (\mathbb{Z}/q)^{\times}$ whose image in $\mathbb{F}_{q^2}$ equals $\alpha^{q+1}$, and every witness that $(\mathrm{diagOneElem}\,q\,(d^{\eta})^{-1}, \alpha^{\eta})$ lies in $\mathrm{hSubgroup}\,q$, the isomorphism $e$ intertwines $\varphi$ with the action of that element through $\mathrm{hFunctionFieldAction}$ on the Drinfeld function field.
--
--   This is the $q = 2$ case, at an auxiliary level rigidified by a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the local description of the semistable model of the modular curve of level $q^2M'$ above a supersingular point $s$ of the level-$M'$ curve in characteristic $q$: the supersingular fibre component is identified, equivariantly for $\Gamma_0(M')$ and for tame inertia, with a quotient of the Drinfeld curve $xy^q - x^qy = 1$, the $q+1$ ends carry annuli with crossing (node) presentations over $W[[U,V]]/(UV - \pi^{E})$, and the complement is covered by smooth-point residue discs. It feeds the downstream assembly of the tube annuli with their widths and of the inertia action on the components of the semistable covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open AlgebraicCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_two_of_dvd
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A) :
    ∃ (FSS : Type) (_ : Field FSS) (_ : Algebra (ResidueField A) FSS)
      (R : RegularProlongation A (fieldBar q M') FSS),
      (∃ t : FSS, Transcendental (ResidueField A) t) ∧
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))) ∧
      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers) ∧
      ∃ (N : Finset (Place (ResidueField ↥A) FSS))
        (Sx : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
        (φx : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥A →+* ↥(Sx Q)))
        (χ₀x : (Q : Place (ResidueField ↥A) FSS) → (↥(Sx Q) →+* ResidueField ↥A))
        (Dx : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
        N.card = q + 1 ∧
        (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

          (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ Sx Q) ∧
          (φx Q).FormallySmooth ∧ (φx Q).FormallyUnramified ∧
          (∀ a : ↥A, ((φx Q (Polynomial.C a) : ↥(Sx Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
          (∀ a : ↥A, χ₀x Q (φx Q (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
          χ₀x Q (φx Q Polynomial.X) = 0 ∧
          (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
            ∃! χ : ↥(Sx Q) →+* ↥A, (∀ a : ↥A, χ (φx Q (Polynomial.C a)) = a) ∧
              (∀ f : ↥(Sx Q), IsLocalRing.residue ↥A (χ f) = χ₀x Q f) ∧ χ (φx Q Polynomial.X) = c) ∧
          (∀ f : ↥(Sx Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
            IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
              algebraMap (ResidueField ↥A) Q.ResidueField (χ₀x Q f)) ∧
          (∃ hR : ((φx Q Polynomial.X : ↥(Sx Q)) : ↥(fieldBar q M')) ∈ R.integers,
            Q.ord (R.residue ⟨((φx Q Polynomial.X : ↥(Sx Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
          (∀ P, P ∈ Dx Q ↔ (P.IsRational ∧ (∀ f : ↥(Sx Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
            (∀ f : ↥(Sx Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀x Q f = 0))) ∧
          (∀ χ : ↥(Sx Q) →+* ↥A, (∀ a : ↥A, χ (φx Q (Polynomial.C a)) = a) →
            (∀ f : ↥(Sx Q), IsLocalRing.residue ↥A (χ f) = χ₀x Q f) →
            ∃! P, P ∈ Dx Q ∧ ∀ f : ↥(Sx Q), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
          (∀ P ∈ Dx Q, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
            ∃ g h : ↥(Sx Q), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ Dx Q, P.ord f = 0) →
            ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(Sx Q))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(Sx Q)) : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ Dx Q, f ∈ P.toValuationSubring) → f ∈ Sx Q)) ∧

        (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ P, P ∈ Dx Q → P ∈ Dx Q' → Q = Q') ∧

        (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

        (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
            ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
          ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
            (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
            (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q))) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                ∀ x : FSS,
                  ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧

        (∀ (g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'))
          (hgA : ∀ x : AlgebraicClosure ℚ, SemilinearAut.baseAut g x ∈ A ↔ x ∈ A)
          (hgR : ∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers)
          (hgj : g • (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) =
            IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')))
          (ψ : ResidueField ↥A ≃+* ResidueField ↥A)
          (hψ : ∀ a : ↥A, ψ (IsLocalRing.residue ↥A a) =
            IsLocalRing.residue ↥A ⟨SemilinearAut.baseAut g (a : AlgebraicClosure ℚ), (hgA (a : AlgebraicClosure ℚ)).mpr a.2⟩)
          (φ : FSS ≃+* FSS)
          (hφ : ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers),
            R.residue ⟨g • f, (hgR f).mpr hf⟩ = φ (R.residue ⟨f, hf⟩)),
          ∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N →
            (∀ y : FSS, y ∈ Q'.toValuationSubring ↔ φ.symm y ∈ Q.toValuationSubring) →
            Q' ∉ N ∧
            ∃ hS : ∀ f : ↥(fieldBar q M'), f ∈ Sx Q ↔ g • f ∈ Sx Q',
              (∀ f : ↥(Sx Q), χ₀x Q' ⟨g • (f : ↥(fieldBar q M')), (hS (f : ↥(fieldBar q M'))).mp f.2⟩ = ψ (χ₀x Q f)) ∧
              (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ Dx Q ↔ g • P ∈ Dx Q')) ∧

        (∀ x x' : Place (ResidueField ↥A) FSS, x ∈ N → x' ∈ N →
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M')
            (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ f ∈ R.integers ↔ f ∈ R.integers),
            R.resAut (levelAutBar q M' ζ γ) hτ • x = x') ∧

        (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M')
            (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ f ∈ R.integers ↔ f ∈ R.integers),
            R.resAut (levelAutBar q M' ζ γ) hτ • Q ≠ Q) ∧

        (∃ (n : ℕ) (g : Fin n → ↥(fieldBar q M')) (hg : ∀ i, g i ∈ R.integers),
          (∀ i, ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q,
            g i ∈ P.toValuationSubring ∧ P.evalAt (g i) ∈ A) ∧
          ∀ f : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → f ∈ Q.toValuationSubring) →
            f ∈ Algebra.adjoin (ResidueField ↥A) (Set.range fun i => R.residue ⟨g i, hg i⟩)) ∧

        (∃ An : Place (ResidueField ↥A) FSS → Annulus A ↥(fieldBar q M'),
          (∀ x ∈ N,
            (∃ hz : (An x).param ∈ R.integers, x.ord (R.residue ⟨(An x).param, hz⟩) = 1 ∧
              ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ (An x).dom, P.ord f = 0) →
                ∀ P ∈ (An x).dom,
                  ∃ h : P.evalAt f * (P.evalAt (An x).param) ^ (-(x.ord (R.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
            ((An x).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
            (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P, P ∈ (An x).dom → P ∉ Dx Q) ∧
            (∀ P ∈ (An x).dom, (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
                (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                  0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
                (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                  ∀ a : A, IsLocalRing.residue A a =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                    ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                      (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A))) ∧
          (∀ x x' : Place (ResidueField ↥A) FSS, x ∈ N → x' ∈ N → ∀ P, P ∈ (An x).dom → P ∈ (An x').dom → x = x') ∧
          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers), ∀ x ∈ N,
              AlgebraicCurve.RegularProlongation.smulDisc τ (An x).dom = (An (R.resAut τ hτ • x)).dom) ∧

          (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
              (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                ∀ a : A, IsLocalRing.residue A a =
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                  ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                    (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) →
            (∃ Q, Q ∉ N ∧ P ∈ Dx Q) ∨ ∃ x, x ∈ N ∧ P ∈ (An x).dom) ∧

          (∀ x ∈ N, ∀ x' ∈ N, x ≠ x' →
            ∃ (g : ↥(fieldBar q M')) (hg : g ∈ R.integers), R.residue ⟨g, hg⟩ ≠ 0 ∧ x.ord (R.residue ⟨g, hg⟩) ≠ 0 ∧
              (∀ P ∈ (An x).dom, P.ord g = 0) ∧
              (∀ P ∈ (An x').dom, g ∈ P.toValuationSubring ∧ ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A))) ∧

          (∃
          (FIx : Place (ResidueField A) FSS → Type) (_ : ∀ x, Field (FIx x)) (_ : ∀ x, Algebra (ResidueField A) (FIx x))
          (Rx : ∀ x : Place (ResidueField A) FSS, RegularProlongation A (fieldBar q M') (FIx x))
          (bx : ∀ x : Place (ResidueField A) FSS, Place (ResidueField A) (FIx x))

          (Λ : Type) (C' : Λ → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : Λ) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
          (_ : ∀ l, IsDomain ↥(C' l)) (_ : ∀ l, IsDiscreteValuationRing ↥(C' l))
          (ϖ' : ∀ l, ↥(C' l)) (l₀ : Λ)
          (Wc : Λ → Type) (_ : ∀ l, CommRing (Wc l)) (_ : ∀ l, IsDomain (Wc l)) (_ : ∀ l, IsDiscreteValuationRing (Wc l))
          (_ : ∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l))
          (πW : ∀ l, Wc l) (E : Λ → ℕ) (E₀ : ℕ)

          (S : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
          (𝒩 : Place (ResidueField A) FSS → Subring (fieldBar q M'))
          (𝒩₀ : Place (ResidueField A) FSS → Λ → Subring (fieldBar q M'))
          (hloc : ∀ nd l, IsLocalRing ↥(𝒩₀ nd l)) (hnoe : ∀ nd l, IsNoetherianRing ↥(𝒩₀ nd l))
          (cx cy cu : Place (ResidueField A) FSS → fieldBar q M'),

          (∀ (l : Λ) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d') ∧
          (∀ l, C' l₀ ≤ C' l) ∧
          ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ≠ 0 ∧
          (∀ a : AlgebraicClosure ℚ, a ∈ A → IsAlgebraic ↥(C' l₀) a) ∧
          (∀ l, Irreducible (πW l)) ∧ (∀ l, 1 ≤ E l) ∧

          (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
            τ ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) = ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ)) ∧

          (∃ w : ℕ, 1 ≤ w ∧ ∃ v : (↥A)ˣ,
            (⟨((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ), hC'A l₀ _ (ϖ' l₀).2⟩ : ↥A) ^ E₀ = (v : ↥A) * ⟨π, hπP⟩ ^ w) ∧

          (∀ nd ∈ N,

            (bx nd).IsRational ∧ nd.IsRational ∧ (∀ P ∈ S nd, P.IsRational) ∧

            (∀ f : fieldBar q M', f ∈ 𝒩 nd ↔ f ∈ (Rx nd).integers ∧ f ∈ R.integers ∧ ∀ P ∈ S nd, f ∈ P.toValuationSubring) ∧
            (∀ f ∈ 𝒩 nd, ∀ P ∈ S nd, P.evalAt f ∈ A) ∧

            cx nd * cy nd = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ * cu nd ∧
            (∀ h₁ : cx nd ∈ (Rx nd).integers, (Rx nd).residue ⟨cx nd, h₁⟩ = 0) ∧
            (∀ h₂ : cx nd ∈ R.integers, nd.ord (R.residue ⟨cx nd, h₂⟩) = 1) ∧
            (∀ h₂ : cy nd ∈ R.integers, R.residue ⟨cy nd, h₂⟩ = 0) ∧
            (∀ h₁ : cy nd ∈ (Rx nd).integers, (bx nd).ord ((Rx nd).residue ⟨cy nd, h₁⟩) = 1) ∧

            (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
              let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S nd ↔ g • P ∈ S nd) ∧ g • cx nd = cx nd ∧ g • cy nd = cy nd) ∧

            (∀ f : fieldBar q M', ∃ (l : Λ) (a b : ↥(𝒩₀ nd l)), (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = (a : fieldBar q M')) ∧

            (∀ f : fieldBar q M', ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd l₀)) (b : ↥(𝒩₀ nd l₀)),
              (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = ∑ i, c i • ((a i : ↥(𝒩₀ nd l₀)) : fieldBar q M')) ∧

            (∀ l, letI : IsLocalRing ↥(𝒩₀ nd l) := hloc nd l;
              𝒩₀ nd l₀ ≤ 𝒩₀ nd l ∧ 𝒩₀ nd l ≤ 𝒩 nd ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S nd ↔
                (∀ f : fieldBar q M', f ∈ 𝒩₀ nd l → f ∈ P.toValuationSubring) ∧
                (∀ f : ↥(𝒩₀ nd l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
              (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀ nd l) ∧
              (∀ g : ↥(𝒩₀ nd l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
              (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd l)), LinearIndependent ↥(C' l) c →
                ∑ i, c i • ((a i : ↥(𝒩₀ nd l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧

              (∃ Bx : Subring (fieldBar q M'),
                (∀ f : fieldBar q M', f ∈ Bx → f ∈ 𝒩₀ nd l) ∧
                cx nd ∈ Bx ∧ cy nd ∈ Bx ∧ cu nd ∈ Bx ∧
                (∀ f : fieldBar q M', f ∈ 𝒩₀ nd l ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
                  (∀ hh : h ∈ 𝒩₀ nd l, IsUnit (⟨h, hh⟩ : ↥(𝒩₀ nd l))) ∧ f * h = g) ∧
                (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
                  ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
                    (↑T : Set (fieldBar q M'))))) ∧
              cx nd ∈ 𝒩₀ nd l ∧ cy nd ∈ 𝒩₀ nd l ∧ (∃ hu : cu nd ∈ 𝒩₀ nd l, IsUnit (⟨cu nd, hu⟩ : ↥(𝒩₀ nd l))) ∧
              ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l))
                (ι : AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l) ≃+* UVCrossingModel (Wc l) (πW l ^ E l)),
                (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l,
                  σ (πW l) = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ o : Wc l, ι (σ o) = const (πW l ^ E l) o) ∧
                (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l),
                  ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₁ : f.1 ∈ (Rx nd).integers), (Rx nd).residue ⟨f.1, h₁⟩ ≠ 0 →
                  (bx nd).ord ((Rx nd).residue ⟨f.1, h₁⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
                      ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * V (πW l ^ E l) ^ n ∈
                        Ideal.span {const (πW l ^ E l) (πW l), U (πW l ^ E l)}) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
                  nd.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
                      ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * U (πW l ^ E l) ^ n ∈
                        Ideal.span {const (πW l ^ E l) (πW l), V (πW l ^ E l)}))) ∧

          (∃ (hJK : ModularCurve.jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M') (a₀ : AlgebraicClosure ℚ) (ha₀ : a₀ ∈ A)
             (hR : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀ ∈ R.integers),
            R.residue ⟨_, hR⟩ = 0 ∧
            (IsLocalRing.residue ↥A ⟨a₀, ha₀⟩) ^ q = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField ↥A) M') ∧
            ∃ (c' : AlgebraicClosure ℚ) (htc : c' • ((⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀) ∈ R.integers),
              R.residue ⟨_, htc⟩ ≠ 0 ∧
              ∀ nd ∈ N, ∃ hC : ((⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀) ∈ (Rx nd).integers,
                (Rx nd).residue ⟨_, hC⟩ ≠ 0 ∧
                nd.ord (R.residue ⟨_, htc⟩) = -((bx nd).ord ((Rx nd).residue ⟨_, hC⟩))) ∧

          (∀ nd ∈ N, ∀ nd' ∈ N, ∀ P, P ∈ S nd → P ∈ S nd' → nd = nd') ∧

          (∀ nd ∈ N, ∀ P ∈ S nd, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              ∀ a : A, residue A a =
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧

          (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∃ τN : Place (ResidueField A) FSS → Place (ResidueField A) FSS,
            ∀ nd ∈ N, τN nd ∈ N ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), (levelAutBar q M' ζ' γ) • P ∈ S nd ↔ P ∈ S (τN nd)) ∧
              ((Rx nd).integers).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = (Rx (τN nd)).integers) ∧

          (∀ τ ∈ Subgroup.closure {τ : (fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] (fieldBar q M') |
                ∃ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ' γ},
            ∀ (hτ : ∀ f : fieldBar q M', τ f ∈ R.integers ↔ f ∈ R.integers), ∀ nd ∈ N,
              R.resAut τ hτ • nd ∈ N ∧
              AlgebraicCurve.RegularProlongation.smulDisc τ (S nd) = S (R.resAut τ hτ • nd)) ∧

          (∀ nd ∈ N, S nd = (An nd).dom) ∧

          (∀ nd ∈ N, ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ (Rx nd).integers) ∧

          (∀ nd ∈ N, ∃ j : modularFunctionFieldC (ResidueField A) M' →+* FIx nd,
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ (Rx nd).integers,
                (Rx nd).residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
            ∀ g : modularFunctionFieldC (ResidueField A) M',
              g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
                j g ∈ (bx nd).toValuationSubring))) ∧

        (∀ (ι : GaloisField q 2 →+* ResidueField ↥A),
          letI : Algebra (GaloisField q 2) (ResidueField ↥A) := ι.toAlgebra
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            ∀ (ζ : Idx q), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ ∃ (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
              (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
                ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                  (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                  ∀ x : FSS,
                    ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                      DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) ∧
              (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
                ι (α : GaloisField q 2) = A.tameCharacter π τ →
                ∀ (g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M')),
                  g = ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ →
                (∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers) ∧
                ∀ (hst : ∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers)
                  (φ : FSS ≃+* FSS),
                  (∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers),
                    R.residue ⟨g • f, (hst f).mpr hf⟩ = φ (R.residue ⟨f, hf⟩)) →
                  ∀ (d : (ZMod q)ˣ), algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1) →
                    ∀ (hmem : (diagOneElem q (d ^ η)⁻¹, α ^ η) ∈ DrinfeldCurve.hSubgroup q),
                      ∀ x : FSS,
                        ((e (φ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                          DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) := by sorry
