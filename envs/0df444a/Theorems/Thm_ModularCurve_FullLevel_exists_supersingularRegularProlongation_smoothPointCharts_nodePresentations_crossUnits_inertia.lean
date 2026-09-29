-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/09ffbdac-9718-51a5-ac82-7967741515c9
-- title:
--   Supersingular prolongation: charts, node annuli, cross units, inertia
-- statement:
--   Throughout, $\overline{\mathbb{Q}}$ denotes `AlgebraicClosure ℚ`; for a field $K$ and an extension $F$, a *place* of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, different from $F$, whose ideals are principal, `P.ord` is minus the logarithm of the associated $\mathbb{Z}$-valued adic valuation, `P.evalAt f` is the element of $K$ corresponding to the residue of $f$ when $f$ is $P$-integral (and $0$ otherwise), and `P.IsRational` says that $K \to$ `P.ResidueField` is surjective.
--
--   **Data and hypotheses.** A prime $q$ with $5 \le q$; a non-zero natural number $M'$ with $q \nmid M'$; a valuation subring $A \subseteq \overline{\mathbb{Q}}$ for which $q$ is a non-unit of $A$ (the predicate `LiesOverPrime`), with residue field $\kappa =$ `ResidueField A`; a finite set $W$ of places of `modularFunctionFieldC κ M'` $= \kappa(j_q, j_{q,M'})$ over $\kappa$ such that $W$ consists exactly of the places lying in `ssPlaces q M' κ`, i.e. those satisfying the predicate `IsSupersingularPlace`; the inclusion `hle` of `modularFunctionFieldBar M'` (the base change to $\overline{\mathbb{Q}}$, inside `LaurentSeries (AlgebraicClosure ℚ)`, of the full level-$M'$ modular function field) into `fieldBar q M'` $=$ `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, where `levelH q M'` is the kernel of $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$; a constant reduction $R_0$ of $A$ on `modularFunctionFieldBar M'` with values in `modularFunctionFieldC κ M'`, that is: a valuation subring $R_0.\mathrm{integers}$ whose intersection with the constants is $A$, a surjective residue homomorphism onto `modularFunctionFieldC κ M'` with kernel the maximal ideal and compatible with the residue map of $A$, the scaling property that every non-zero element becomes a non-zero residue after multiplication by a constant, together with a map `placeMap` on places preserving degrees and compatible with divisor push-forward; the hypothesis `hR₀`, which states that every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}$ lies in `modularFunctionFieldBar M'` already lies in $R_0.\mathrm{integers}$, with $R_0$-residue the coefficientwise reduction of $y$ modulo the maximal ideal of $A$; a chosen element $s \in W$; and an element $\pi \in A$ with $\pi^{q^2-1} = q$.
--
--   The element of `modularFunctionFieldBar M'` given by the coefficientwise image of the rational Laurent series `jq` is written $j$ below. A function $f$ is said to be *$j$-regular* if $0 \le P.\mathrm{ord}(f)$ at every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ at which $0 \le P.\mathrm{ord}(j)$. A place $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ is said to *reduce to $s$* if for every $j$-regular $f \in R_0.\mathrm{integers}$ whose $R_0$-residue lies in the valuation subring of $s$, and every $a \in A$ with residue $s.\mathrm{evalAt}(R_0\text{-residue of } f)$, the difference $P.\mathrm{evalAt}(f) - a$ lies in $A$ and in fact in the maximal ideal of $A$.
--
--   **Conclusion.** There exist a field $F_{ss}$, an algebra structure of $\kappa$ on it, and a regular prolongation $R$ of $A$ on `fieldBar q M'` with residue field $F_{ss}$ (a valuation subring $R.\mathrm{integers}$ meeting the constants exactly in $A$, a surjective residue map onto $F_{ss}$ with kernel the maximal ideal, compatible with the residue map of $A$, and with the scaling property), such that:
--
--   (1) some element of $F_{ss}$ is transcendental over $\kappa$;
--
--   (2) for every $j$-regular $f \in R_0.\mathrm{integers}$ whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` lies in $R.\mathrm{integers}$ and its $R$-residue is the image under $\kappa \to F_{ss}$ of $s.\mathrm{evalAt}$ of that $R_0$-residue;
--
--   (3) for every $\zeta \in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in \Gamma_0(M')$, the subring $R.\mathrm{integers}$ is invariant under pullback along `levelAutBar q M' ζ γ` (the automorphism of `fieldBar q M'` over $\overline{\mathbb{Q}}$ characterised by the $q$-expansion condition `IsLevelAutBar`, and the identity if no such automorphism exists);
--
--   and there exist a finite set $N$ of places of $F_{ss}$ over $\kappa$, subrings $S_Q \subseteq$ `fieldBar q M'`, ring homomorphisms $\varphi_Q : A[X] \to S_Q$ and $\chi_{0,Q} : S_Q \to \kappa$, and sets $D_Q$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$, indexed by the places $Q$ of $F_{ss}$ over $\kappa$, with the following properties.
--
--   **(A) Cardinality.** $N$ has exactly $q+1$ elements.
--
--   **(B) Smooth-point charts.** For every $Q \notin N$: the image of every $a \in A$ in `fieldBar q M'` lies in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C\,a)$ has image the constant $a$, and $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$; $\chi_{0,Q}(\varphi_Q(X)) = 0$; for every $c \in A$ with residue $0$ there is a unique ring homomorphism $\chi : S_Q \to A$ with $\chi(\varphi_Q(C\,a)) = a$ for all $a \in A$, with residue $\circ\, \chi = \chi_{0,Q}$, and with $\chi(\varphi_Q(X)) = c$; every $f \in S_Q$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$, and the residue there equals the image of $\chi_{0,Q}(f)$ under $\kappa \to Q.\mathrm{ResidueField}$; the $R$-residue of $\varphi_Q(X)$ has $Q$-order $1$; $D_Q$ consists exactly of those places $P$ that are rational, are such that every $f \in S_Q$ is $P$-integral with $P.\mathrm{evalAt}(f) \in A$, and satisfy, for every $f \in S_Q$, the equivalence of $A$-valuation of $P.\mathrm{evalAt}(f)$ being $<1$ with $\chi_{0,Q}(f) = 0$; every $\chi : S_Q \to A$ fixing the constants and lifting $\chi_{0,Q}$ comes from a unique $P \in D_Q$, in the sense that $P.\mathrm{evalAt}(f) = \chi(f)$ for all $f \in S_Q$; for $P \in D_Q$, an element $f$ of `fieldBar q M'` is $P$-integral if and only if $f \cdot h = g$ for some $g, h \in S_Q$ with $P.\mathrm{evalAt}(h) \ne 0$; a unit principle holds: if $f \ne 0$ has $P.\mathrm{ord}(f) = 0$ for all $P \in D_Q$, then $c\,f$ is a unit of $S_Q$ for some non-zero constant $c \in \overline{\mathbb{Q}}$; and any $f \in R.\mathrm{integers}$ that is $P$-integral for all $P \in D_Q$ lies in $S_Q$.
--
--   **(C) Disjointness of the discs.** If $Q, Q' \notin N$ and some place lies in both $D_Q$ and $D_{Q'}$, then $Q = Q'$.
--
--   **(D) No cusps in the discs.** For $Q \notin N$ and $P \in D_Q$, the image of $j$ in `fieldBar q M'` satisfies $0 \le P.\mathrm{ord}$.
--
--   **(E) Level equivariance.** For every $\tau$ in the subgroup of automorphisms of `fieldBar q M'` over $\overline{\mathbb{Q}}$ generated by the `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$, and every proof that $\tau$ preserves $R.\mathrm{integers}$: the induced residue automorphism $R.\mathrm{resAut}\,\tau$ permutes $N$ (membership in $N$ is preserved in both directions), and for $Q \notin N$ the transported disc $\{P : \tau^{-1}\cdot P \in D_Q\}$ equals $D_{R.\mathrm{resAut}\,\tau \cdot Q}$.
--
--   **(F) Drinfeld identification.** For every algebra structure of $\mathbb{F}_{q^2} =$ `GaloisField q 2` on $\kappa$, assuming [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, and for every $\zeta \in$ `Idx q`, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and a $\kappa$-algebra isomorphism $e$ from $F_{ss}$ onto [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) (the field fixed, inside the fraction field of `CoordRing q κ`, by the subgroup generated by the `hFunctionFieldAction` of the elements $(1, \zeta')$, $\zeta' \in C_s$) such that $\mathrm{card}\,C_s = 2\cdot$ `placeWidthChar q M' s` and such that, for $\gamma \in \Gamma_0(M')$ with `levelAutBar q M' ζ γ⁻¹` preserving $R.\mathrm{integers}$ and with $(\mathrm{redQ}\,q\,\gamma, 1)$ in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), $e$ intertwines $R.\mathrm{resAut}$ of that level automorphism with the action of $(\mathrm{redQ}\,q\,\gamma, 1)$ on the Drinfeld function field.
--
--   **(G) Transport under semilinear automorphisms.** Let $g$ be a semilinear automorphism of `fieldBar q M'` over $\overline{\mathbb{Q}}$ (a pair consisting of a ring automorphism of the field and one of $\overline{\mathbb{Q}}$, compatible with the structure map) such that the base automorphism preserves $A$ in both directions, $g$ preserves $R.\mathrm{integers}$ in both directions, and $g$ fixes the image of $j$; let $\psi$ be a ring automorphism of $\kappa$ compatible with the base automorphism of $g$ via the residue map of $A$, and $\varphi$ a ring automorphism of $F_{ss}$ with $R$-residue of $g\cdot f$ equal to $\varphi(R$-residue of $f)$ for all $f \in R.\mathrm{integers}$. Then for $Q \notin N$ and any place $Q'$ whose valuation subring is the $\varphi$-transport of that of $Q$ (i.e. $y \in Q'$ iff $\varphi^{-1}(y) \in Q$) one has $Q' \notin N$, and $f \in S_Q \iff g\cdot f \in S_{Q'}$, with $\chi_{0,Q'}(g \cdot f) = \psi(\chi_{0,Q}(f))$ for $f \in S_Q$, and $P \in D_Q \iff g\cdot P \in D_{Q'}$.
--
--   **(H) Transitivity on $N$.** For any $x, x' \in N$ there are $\zeta$ and $\gamma \in \Gamma_0(M')$ with `levelAutBar q M' ζ γ` preserving $R.\mathrm{integers}$ and $R.\mathrm{resAut}$ of it carrying $x$ to $x'$.
--
--   **(I) Mobility off $N$.** For every $Q \notin N$ there are $\zeta$ and $\gamma \in \Gamma_0(M')$ with `levelAutBar q M' ζ γ` preserving $R.\mathrm{integers}$ and $R.\mathrm{resAut}$ of it moving $Q$.
--
--   **(J) Finite generation of the affine ring.** There are finitely many elements $g_1,\dots,g_n$ of $R.\mathrm{integers}$ such that each $g_i$ is $P$-integral with $P.\mathrm{evalAt}(g_i) \in A$ for every $P \in D_Q$ and every $Q \notin N$, and such that every $f \in F_{ss}$ which is integral at all $Q \notin N$ lies in the $\kappa$-subalgebra of $F_{ss}$ generated by the $R$-residues of the $g_i$.
--
--   **(K) Node annuli.** There is a family $\mathrm{An}$ of annuli over $A$ in `fieldBar q M'` indexed by the places of $F_{ss}$ over $\kappa$ — each consisting of a set $\mathrm{dom}$ of places, a parameter, and a modulus in the maximal ideal of $A$, subject to the `Annulus` axioms: the places of $\mathrm{dom}$ are rational, the parameter is integral there with value a non-zero element of the maximal ideal dividing the modulus, values of the parameter in the maximal ideal dividing the modulus are attained by a unique place of $\mathrm{dom}$, $\mathrm{ord}$ of the parameter minus its value is $1$, and a unit principle holds — such that:
--
--   (K1) for $x \in N$: the parameter of $\mathrm{An}\,x$ lies in $R.\mathrm{integers}$ and its $R$-residue has $x$-order $1$; for every $f \in R.\mathrm{integers}$ with non-zero $R$-residue and $P.\mathrm{ord}(f) = 0$ for all $P \in (\mathrm{An}\,x).\mathrm{dom}$, and every such $P$, the element $P.\mathrm{evalAt}(f)\cdot P.\mathrm{evalAt}(\text{parameter})^{-x.\mathrm{ord}(R\text{-residue of } f)}$ lies in $A$ and is a unit there (the cross-unit clause); the modulus of $\mathrm{An}\,x$ is non-zero; $(\mathrm{An}\,x).\mathrm{dom}$ is disjoint from every $D_Q$ with $Q \notin N$; and every $P \in (\mathrm{An}\,x).\mathrm{dom}$ reduces to $s$;
--
--   (K2) distinct $x, x' \in N$ have disjoint annulus domains;
--
--   (K3) for $\tau$ in the level subgroup as in (E) preserving $R.\mathrm{integers}$ and $x \in N$, the transported domain $\{P : \tau^{-1}\cdot P \in (\mathrm{An}\,x).\mathrm{dom}\}$ equals $(\mathrm{An}(R.\mathrm{resAut}\,\tau \cdot x)).\mathrm{dom}$;
--
--   (K4) covering: every rational place of `fieldBar q M'` over $\overline{\mathbb{Q}}$ that reduces to $s$ lies either in $D_Q$ for some $Q \notin N$ or in $(\mathrm{An}\,x).\mathrm{dom}$ for some $x \in N$;
--
--   (K5) separation of the ends: for $x \ne x'$ in $N$ there is $g \in R.\mathrm{integers}$ with non-zero $R$-residue whose $x$-order is non-zero, with $P.\mathrm{ord}(g) = 0$ on $(\mathrm{An}\,x).\mathrm{dom}$, while on $(\mathrm{An}\,x').\mathrm{dom}$ the function $g$ is integral with value a unit of $A$;
--
--   (K6) **node presentations.** There are: fields $F_x$ with $\kappa$-algebra structures, regular prolongations $R_x$ of $A$ on `fieldBar q M'` with residue field $F_x$ and places $b_x$ of $F_x$ over $\kappa$, indexed by the places $x$ of $F_{ss}$ over $\kappa$; an index type $\Lambda$ with subrings $C'_l \subseteq \overline{\mathbb{Q}}$ contained in $A$, each a domain and a discrete valuation ring, elements $\varpi'_l \in C'_l$, a base index $l_0$; complete discrete valuation domains $W_l$ with elements $\pi_{W,l}$, exponents $E_l \in \mathbb{N}$ and $E_0 \in \mathbb{N}$; sets $S_{nd}$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$, subrings $\mathcal{N}_{nd}$ and $\mathcal{N}_{0,nd,l}$ of `fieldBar q M'`, the latter local and Noetherian, and elements $c^x_{nd}, c^y_{nd}, c^u_{nd}$, all indexed by the places $nd$ of $F_{ss}$ over $\kappa$; such that: an element of $C'_l$ has residue $0$ in $\kappa$ exactly when it is divisible by $\varpi'_l$ in $C'_l$; $C'_{l_0} \le C'_l$ for all $l$; $\varpi'_{l_0} \ne 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_{W,l}$ is irreducible and $1 \le E_l$; every $\tau$ in the inertia subgroup of $A$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with `tameCharacter A π τ` $= 1$ fixes $\varpi'_{l_0}$; and $(\varpi'_{l_0})^{E_0} = v\,\pi^w$ in $A$ for some unit $v$ of $A$ and some $w \ge 1$.
--
--   Moreover, for every $nd \in N$: $b_{nd}$, $nd$ and all places in $S_{nd}$ are rational; $\mathcal{N}_{nd}$ consists exactly of those $f$ lying in $(R_{nd}).\mathrm{integers}$, in $R.\mathrm{integers}$ and integral at every $P \in S_{nd}$, and for such $f$ the values $P.\mathrm{evalAt}(f)$, $P \in S_{nd}$, lie in $A$; the crossing relation $c^x_{nd}\,c^y_{nd} = (\varpi'_{l_0})^{E_0}\,c^u_{nd}$ holds (with $\varpi'_{l_0}$ viewed in `fieldBar q M'`); $c^x_{nd}$ has $R_{nd}$-residue $0$ and its $R$-residue has $nd$-order $1$, while $c^y_{nd}$ has $R$-residue $0$ and its $R_{nd}$-residue has $b_{nd}$-order $1$ (each stated under the hypothesis that the element lies in the relevant ring of integers); for every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ with trivial tame character, the semilinear automorphism $g =$ `arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ` (coefficientwise action of $\tau$ on Laurent series) preserves $S_{nd}$ and fixes $c^x_{nd}$ and $c^y_{nd}$; every element of `fieldBar q M'` is a quotient of two elements of $\mathcal{N}_{0,nd,l}$ for some $l$, and becomes, after multiplication by a non-zero element of $\mathcal{N}_{0,nd,l_0}$, a finite $\overline{\mathbb{Q}}$-linear combination of elements of $\mathcal{N}_{0,nd,l_0}$; and for every $l$: $\mathcal{N}_{0,nd,l_0} \le \mathcal{N}_{0,nd,l} \le \mathcal{N}_{nd}$; a place $P$ lies in $S_{nd}$ exactly when $\mathcal{N}_{0,nd,l}$ is contained in its valuation subring and every non-unit of $\mathcal{N}_{0,nd,l}$ has value in the maximal ideal of $A$; $C'_l$ maps into $\mathcal{N}_{0,nd,l}$; every element of $\mathcal{N}_{0,nd,l}$ differs from the image of some element of $C'_l$ by a non-unit; any family of elements of $\mathcal{N}_{0,nd,l}$ with a vanishing combination with $C'_l$-linearly independent coefficients from $\overline{\mathbb{Q}}$ is zero; $c^x_{nd}, c^y_{nd} \in \mathcal{N}_{0,nd,l}$ and $c^u_{nd}$ is a unit there; and there are a ring homomorphism $\sigma$ from $W_l$ into the adic completion of $\mathcal{N}_{0,nd,l}$ at its maximal ideal and a ring isomorphism $\iota$ of that completion with `UVCrossingModel (Wc l) (πW l ^ E l)` (the quotient of the two-variable power series ring over $W_l$ by `uvCrossingIdeal`) such that $\sigma(\pi_{W,l})$ is the image of $\varpi'_l$, $\iota \circ \sigma$ is the constant map `const`, every element of $C'_l$ whose image lies in $\mathcal{N}_{0,nd,l}$ is in the image of $\sigma$, and the two order-matching clauses hold: an $f \in \mathcal{N}_{0,nd,l}$ with non-zero $R_{nd}$-residue of $b_{nd}$-order $n$ satisfies $\iota(f) \equiv \gamma\,V^n$ modulo the ideal generated by `const (πW l)` and $U$ for some unit $\gamma$, and an $f$ with non-zero $R$-residue of $nd$-order $n$ satisfies $\iota(f) \equiv \gamma\,U^n$ modulo the ideal generated by `const (πW l)` and $V$ for some unit $\gamma$.
--
--   Finally, within (K6): the sets $S_{nd}$, $nd \in N$, are pairwise disjoint; every $P \in S_{nd}$ reduces to $s$; for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$ there is a map $\tau_N$ on places preserving $N$ with $(\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma)\cdot P \in S_{nd} \iff P \in S_{\tau_N(nd)}$ and with the pullback of $(R_{nd}).\mathrm{integers}$ along that level automorphism equal to $(R_{\tau_N(nd)}).\mathrm{integers}$; for $\tau$ in the level subgroup preserving $R.\mathrm{integers}$ and $nd \in N$, $R.\mathrm{resAut}\,\tau \cdot nd \in N$ and the transported set $\{P : \tau^{-1}\cdot P \in S_{nd}\}$ equals $S_{R.\mathrm{resAut}\,\tau\cdot nd}$; $S_{nd} = (\mathrm{An}\,nd).\mathrm{dom}$; and the image in `fieldBar q M'` of every element of $R_0.\mathrm{integers}$ lies in $(R_{nd}).\mathrm{integers}$.
--
--   **(L) Drinfeld identification with inertia.** For every ring homomorphism $\iota : \mathbb{F}_{q^2} \to \kappa$, taken as the algebra structure, and assuming [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, there is a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ with $\mathrm{card}\,C_s = 2\cdot$ `placeWidthChar q M' s` such that for every $\zeta \in$ `Idx q` there is a $\kappa$-algebra isomorphism $e$ from $F_{ss}$ onto [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) with: the $\Gamma_0(M')$-equivariance of (F), namely for $\gamma \in \Gamma_0(M')$ with `levelAutBar q M' ζ γ⁻¹` preserving $R.\mathrm{integers}$ and $(\mathrm{redQ}\,q\,\gamma, 1) \in$ `hSubgroup q`, $e$ intertwines $R.\mathrm{resAut}$ of that automorphism with the action of $(\mathrm{redQ}\,q\,\gamma, 1)$; and, for every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ and every unit $\alpha$ of $\mathbb{F}_{q^2}$ with $\iota(\alpha) =$ `A.tameCharacter π τ`, and every semilinear automorphism $g$ equal to `arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`: $g$ preserves $R.\mathrm{integers}$ in both directions, and for every ring automorphism $\varphi$ of $F_{ss}$ compatible with $R$-residues and $g$, every unit $d$ of $\mathbb{Z}/q$ whose image in $\mathbb{F}_{q^2}$ is $\alpha^{q+1}$, and $(\mathrm{diagOneElem}\,q\,(d^q)^{-1}, \alpha^q)$ in `hSubgroup q`, the isomorphism $e$ carries $\varphi$ to the action of that element of `hSubgroup q` on the Drinfeld function field.
--
--   This is the single-package statement of the supersingular reduction of the modular curve of level $\Gamma_H(q^2M')$ at a place above $q$: one regular prolongation carries simultaneously the smooth-point charts and residue discs, the $q+1$ node annuli with their cross-unit property and formal crossing presentations $xy = \varpi^{E_0}u$, the level-$\Gamma_0(M')$ and inertia equivariance, and the identification of the supersingular component with a quotient of the Drinfeld curve $xy^q - x^qy = 1$. It is obtained by discarding conjuncts of [`ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ`](thm.html#ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ), and is the form used downstream by the semistable-covering and node-chart results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia.lean

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

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ (Rx nd).integers))) ∧

        (∀ (ι : GaloisField q 2 →+* ResidueField ↥A),
          letI : Algebra (GaloisField q 2) (ResidueField ↥A) := ι.toAlgebra
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            ∀ (ζ : Idx q), ∃ (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
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
                    ∀ (hmem : (diagOneElem q (d ^ q)⁻¹, α ^ q) ∈ DrinfeldCurve.hSubgroup q),
                      ∀ x : FSS,
                        ((e (φ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                          DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) := by sorry
