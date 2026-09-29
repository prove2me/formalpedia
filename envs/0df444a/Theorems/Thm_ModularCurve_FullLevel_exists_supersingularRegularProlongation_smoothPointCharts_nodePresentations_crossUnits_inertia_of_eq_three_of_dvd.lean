-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/67b343f8-05e3-579e-b736-6132c9681b37
-- title:
--   Supersingular prolongation at q=3: charts, node annuli, Drinfeld action
-- statement:
--   Throughout, write $\kappa := \mathrm{ResidueField}\,A$ for the residue field of the valuation subring $A$, $F :=$ `fieldBar q M'` for the base change to $\bar{\mathbb Q}$ (inside Laurent series over $\bar{\mathbb Q}$) of the function field `xHFunctionField (q^2 * M') (levelH q M')` of level $q^2M'$ with $H =$ `levelH q M'` the kernel of the unit reduction `ZMod.unitsMap (dvd_sq_mul q M')`, and $F_0 :=$ `modularFunctionFieldBar M'`, the base change to $\bar{\mathbb Q}$ of the full modular function field of level $M'$. The element $j \in F_0$ is the one given by the coefficientwise image `coeffEmb (AlgebraicClosure ℚ) jq` of the $q$-expansion of $j$. Places are always places in the sense of the structure `Place`: a valuation subring of the ambient field, proper, containing the image of the base field and a principal ideal ring; `Place.ord` is the associated $\mathbb Z$-valued order, `Place.IsRational` says that the base field surjects onto the residue field of the place, and `Place.evalAt f` is the resulting value in the base field (zero if $f$ is not in the valuation subring).
--
--   Data and hypotheses. A prime $q$ with $q = 3$; a nonzero natural number $M'$ with $q \nmid M'$; a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$ (a rigidity guard on the auxiliary level). A valuation subring $A \subseteq \bar{\mathbb Q}$ with `A.LiesOverPrime q`, that is, $q$ is a non-unit of $A$. A finite set $W$ of places of `modularFunctionFieldC κ M'` $= \kappa(j, j_{M'})$ over $\kappa$, with `hW` saying that $W$ consists exactly of the places satisfying the predicate `IsSupersingularPlace q M' κ` (the set `ssPlaces q M' κ`), together with a distinguished element $s \in W$. The inclusion `hle` of intermediate fields $F_0 \le F$. A constant reduction $R_0$ of $A$ from $F_0$ to $\kappa(j,j_{M'})$, i.e. a valuation subring `R₀.integers` of $F_0$, a surjective residue map onto $\kappa(j,j_{M'})$ with kernel the maximal ideal, meeting $A$ correctly under the structure map, such that every nonzero element of $F_0$ has a $\bar{\mathbb Q}$-multiple in `R₀.integers` with nonzero residue, together with a map `placeMap` on places preserving degrees and compatible with order functions. The hypothesis `hR₀` states that every Laurent series $y$ over $A$ whose coefficientwise image in Laurent series over $\bar{\mathbb Q}$ lies in $F_0$ belongs to `R₀.integers`, with residue the coefficientwise reduction of $y$ to $\kappa$. Finally an element $\pi \in \bar{\mathbb Q}$ with $\pi^{q^2-1} = q$ and $\pi \in A$.
--
--   Conclusion. There exist a type $F_{ss}$ carrying a field structure and a $\kappa$-algebra structure, and a regular prolongation $R$ of $A$ from $F$ to $F_{ss}$ (a valuation subring `R.integers` of $F$, a surjective residue map onto $F_{ss}$ with kernel the maximal ideal, compatible with $A$ under the structure map, and such that every nonzero element of $F$ has a $\bar{\mathbb Q}$-multiple in `R.integers` with nonzero residue), such that the following hold.
--
--   (1) $F_{ss}$ contains an element transcendental over $\kappa$.
--
--   (2) Specialisation over $s$: for every $f \in$ `R₀.integers` such that $0 \le P.\mathrm{ord}(f)$ at every place $P$ of $F_0$ over $\bar{\mathbb Q}$ at which $0 \le P.\mathrm{ord}(j)$, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $F$ lies in `R.integers` and its $R$-residue is the image under $\kappa \to F_{ss}$ of $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$.
--
--   (3) Level invariance: for every $\zeta$ in `Idx q` (a primitive $q$-th root of unity in $\bar{\mathbb Q}$) and every $\gamma \in \Gamma_0(M') \le \mathrm{SL}_2(\mathbb Z)$, the pullback of `R.integers` along the level automorphism `levelAutBar q M' ζ γ` of $F$ equals `R.integers`.
--
--   (4) There exist a finite set $N$ of places of $F_{ss}$ over $\kappa$, and, indexed by places $Q$ of $F_{ss}$ over $\kappa$, subrings $S_Q \subseteq F$, ring homomorphisms $\varphi_Q : A[X] \to S_Q$, ring homomorphisms $\chi_{0,Q} : S_Q \to \kappa$, and sets $D_Q$ of places of $F$ over $\bar{\mathbb Q}$, with $\#N = q+1$ and the following properties.
--
--   (4a) Smooth-point charts: for every $Q \notin N$: the image of $A$ in $F$ lies in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C\,a)$ is the image of $a$ in $F$ for $a \in A$, and $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$ in $\kappa$; $\chi_{0,Q}(\varphi_Q X) = 0$; for each $c \in A$ with residue $0$ there is a unique ring homomorphism $\chi : S_Q \to A$ with $\chi(\varphi_Q(C\,a)) = a$ for all $a \in A$, with residue of $\chi(f)$ equal to $\chi_{0,Q}(f)$ for all $f \in S_Q$, and with $\chi(\varphi_Q X) = c$; every $f \in S_Q$ lies in `R.integers`, its $R$-residue lies in the valuation subring of $Q$, and the residue there is the image of $\chi_{0,Q}(f)$ under $\kappa \to Q.\mathrm{ResidueField}$; $\varphi_Q X$ lies in `R.integers` and its $R$-residue has $Q$-order $1$; $D_Q$ consists exactly of the rational places $P$ of $F$ over $\bar{\mathbb Q}$ such that every $f \in S_Q$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f) \in A$, and such that for every $f \in S_Q$ the $A$-valuation of $P.\mathrm{evalAt}(f)$ is $< 1$ if and only if $\chi_{0,Q}(f) = 0$; every ring homomorphism $\chi : S_Q \to A$ restricting to the identity on $A$ via $\varphi_Q \circ C$ and lifting $\chi_{0,Q}$ is realised by a unique $P \in D_Q$, in the sense that $P.\mathrm{evalAt}(f) = \chi(f)$ for all $f \in S_Q$; for $P \in D_Q$, an element $f \in F$ lies in the valuation subring of $P$ if and only if $f = g/h$ with $g, h \in S_Q$ and $P.\mathrm{evalAt}(h) \ne 0$; every nonzero $f \in F$ with $P.\mathrm{ord}(f) = 0$ for all $P \in D_Q$ becomes a unit of $S_Q$ after multiplication by the image of some nonzero $c \in \bar{\mathbb Q}$; and every $f \in$ `R.integers` lying in the valuation subring of every $P \in D_Q$ lies in $S_Q$.
--
--   (4b) The discs are pairwise disjoint: if $Q, Q' \notin N$ and some $P$ lies in both $D_Q$ and $D_{Q'}$, then $Q = Q'$.
--
--   (4c) No cusps on the charts: for $Q \notin N$ and $P \in D_Q$, $0 \le P.\mathrm{ord}$ of the image of $j$ in $F$.
--
--   (4d) Level equivariance of $N$ and of the discs: for every $\tau$ in the subgroup of $\bar{\mathbb Q}$-algebra automorphisms of $F$ generated by the `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$, and every proof that $\tau$ preserves `R.integers`, the induced residue automorphism `R.resAut τ` maps $N$ onto $N$ (membership is equivalent for $Q$ and for its translate) and, for $Q \notin N$, sends $D_Q$ to $D_{\,\mathrm{resAut}(\tau)\cdot Q}$, where the action on sets of places is `smulDisc τ D = {P | τ^{-1}\cdot P \in D}`.
--
--   (4e) Drinfeld identification, first form: for every $\mathbb F_{q^2}$-algebra structure on $\kappa$ (where $\mathbb F_{q^2} =$ `GaloisField q 2`), assuming [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, and for every $\zeta$ in `Idx q`, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb F_{q^2}$ and a $\kappa$-algebra isomorphism $e$ from $F_{ss}$ onto [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32), the fixed field in the Drinfeld function field of the subgroup generated by the actions of the elements $(1,\zeta')$, $\zeta' \in C_s$, such that $\#C_s = 2\,\cdot$ `placeWidthChar q M' s` (the quotient of `jWidthChar q` at the value of `jGeomGen` at $s$ by `placeRamificationJ M' s`), and such that for $\gamma \in \Gamma_0(M')$, given that `levelAutBar q M' ζ γ⁻¹` preserves `R.integers` and that $(\bar\gamma, 1) \in$ [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) for $\bar\gamma =$ `redQ q γ`, the isomorphism $e$ carries the residue automorphism induced by `levelAutBar q M' ζ γ⁻¹` into the action `hFunctionFieldAction q κ ⟨(\bar\gamma,1)⟩` on the Drinfeld function field.
--
--   (4f) Transport along semilinear automorphisms: let $g$ be a semilinear automorphism of $F$ over $\bar{\mathbb Q}$ (an element of `SemilinearAut`, i.e. a pair of ring automorphisms of $F$ and of $\bar{\mathbb Q}$ compatible with the structure map) whose base automorphism preserves $A$ setwise, which preserves `R.integers`, and which fixes the image of $j$; let $\psi$ be a ring automorphism of $\kappa$ compatible with $g$ on $A$, and $\varphi$ a ring automorphism of $F_{ss}$ with $R$-residue of $g\cdot f$ equal to $\varphi$ of the $R$-residue of $f$ for all $f \in$ `R.integers`. Then for places $Q, Q'$ of $F_{ss}$ over $\kappa$ with $Q \notin N$ and $Q'$ the transport of $Q$ along $\varphi$ ($y \in Q'$ iff $\varphi^{-1}(y) \in Q$), one has $Q' \notin N$, and $f \in S_Q$ if and only if $g\cdot f \in S_{Q'}$, with $\chi_{0,Q'}(g \cdot f) = \psi(\chi_{0,Q}(f))$ for $f \in S_Q$, and $P \in D_Q$ if and only if $g \cdot P \in D_{Q'}$.
--
--   (4g) The level group acts transitively on $N$: for $x, x' \in N$ there are $\zeta$ and $\gamma \in \Gamma_0(M')$ with `levelAutBar q M' ζ γ` preserving `R.integers` whose induced residue automorphism sends $x$ to $x'$.
--
--   (4h) For every $Q \notin N$ there are $\zeta$ and $\gamma \in \Gamma_0(M')$ with `levelAutBar q M' ζ γ` preserving `R.integers` whose induced residue automorphism does not fix $Q$.
--
--   (4i) Generation: there are $n$ and elements $g_0,\dots,g_{n-1}$ of `R.integers` such that each $g_i$ lies in the valuation subring of every $P \in D_Q$ with $P.\mathrm{evalAt}(g_i) \in A$, for every $Q \notin N$, and such that every $f \in F_{ss}$ lying in the valuation subring of all places $Q \notin N$ belongs to the $\kappa$-subalgebra of $F_{ss}$ generated by the $R$-residues of the $g_i$.
--
--   (4j) Node annuli. There is an assignment $x \mapsto \mathrm{An}(x)$ of an annulus over $A$ in $F$ (in the sense of the structure `Annulus`: a set `dom` of places, a parameter `param`, a modulus in the maximal ideal of $A$, such that at each place of `dom` the place is rational, the parameter is integral with value in the maximal ideal of $A$, nonzero, and the modulus is the product of that value with an element of the maximal ideal; such that each admissible value is attained at exactly one place of `dom`; such that `param` minus its value has order $1$ at each place of `dom`; and with the unit principle for functions of order $0$ throughout `dom`) to places of $F_{ss}$ over $\kappa$, such that:
--
--   — for $x \in N$: the parameter of $\mathrm{An}(x)$ lies in `R.integers` and its $R$-residue has $x$-order $1$; for every $f \in$ `R.integers` with nonzero $R$-residue and with $P.\mathrm{ord}(f) = 0$ at all $P \in \mathrm{An}(x).\mathrm{dom}$, and every such $P$, the element $P.\mathrm{evalAt}(f)\cdot P.\mathrm{evalAt}(\mathrm{param})^{-x.\mathrm{ord}(R\text{-residue of } f)}$ lies in $A$ and is a unit there; the modulus of $\mathrm{An}(x)$ is nonzero in $\bar{\mathbb Q}$; no place of $\mathrm{An}(x).\mathrm{dom}$ lies in $D_Q$ for any $Q \notin N$; and every $P \in \mathrm{An}(x).\mathrm{dom}$ specialises over $s$, in the sense that for every $f \in$ `R₀.integers` regular wherever $j$ is (as in (2)) whose $R_0$-residue lies in the valuation subring of $s$, and every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference $P.\mathrm{evalAt}(f) - a$ lies in $A$ and in its maximal ideal;
--
--   — distinct $x, x' \in N$ have disjoint annulus domains;
--
--   — for $\tau$ in the subgroup generated by the level automorphisms `levelAutBar q M' ζ γ`, $\gamma \in \Gamma_0(M')$, preserving `R.integers`, and $x \in N$, the transport `smulDisc τ` of $\mathrm{An}(x).\mathrm{dom}$ is $\mathrm{An}(\mathrm{resAut}(\tau)\cdot x).\mathrm{dom}$;
--
--   — covering: every rational place $P$ of $F$ over $\bar{\mathbb Q}$ which specialises over $s$ in the above sense lies either in $D_Q$ for some $Q \notin N$ or in $\mathrm{An}(x).\mathrm{dom}$ for some $x \in N$;
--
--   — separation: for $x \ne x'$ in $N$ there is $g \in$ `R.integers` with nonzero $R$-residue, with $x.\mathrm{ord}$ of that residue nonzero, with $P.\mathrm{ord}(g) = 0$ for all $P \in \mathrm{An}(x).\mathrm{dom}$, and such that at every $P \in \mathrm{An}(x').\mathrm{dom}$ the element $g$ is integral with $P.\mathrm{evalAt}(g)$ a unit of $A$;
--
--   — node presentations: there exist, indexed by places $x$ of $F_{ss}$ over $\kappa$, types $FI_x$ with field and $\kappa$-algebra structures, regular prolongations $R_x$ of $A$ from $F$ to $FI_x$ and places $b_x$ of $FI_x$ over $\kappa$; a type $\Lambda$, subrings $C'_l \subseteq \bar{\mathbb Q}$ all contained in $A$, each a domain and a discrete valuation ring, elements $\varpi'_l \in C'_l$, a base index $l_0$; rings $W_l$ which are complete discrete valuation domains (adically complete for the maximal ideal), elements $\pi_{W,l} \in W_l$, exponents $E : \Lambda \to \mathbb N$ and $E_0 \in \mathbb N$; sets $S_{nd}$ of places of $F$ over $\bar{\mathbb Q}$, subrings $\mathcal N_{nd} \subseteq F$ and $\mathcal N_{0,nd,l} \subseteq F$ (each local and Noetherian by the given witnesses), and elements $c^x_{nd}, c^y_{nd}, c^u_{nd} \in F$, such that: for $d \in C'_l$, the residue of $d$ in $\kappa$ vanishes if and only if $d \in \varpi'_l\, C'_l$; $C'_{l_0} \subseteq C'_l$ for all $l$; $\varpi'_{l_0} \ne 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_{W,l}$ is irreducible and $1 \le E(l)$; every $\tau$ in `A.inertiaSubgroupIn ℚ` (the image in $\mathrm{Aut}(\bar{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$) with `A.tameCharacter π τ` $= 1$ fixes $\varpi'_{l_0}$; and there are $w \ge 1$ and a unit $v$ of $A$ with $(\varpi'_{l_0})^{E_0} = v\,\pi^w$ in $A$. Moreover, for every $nd \in N$: $b_{nd}$, $nd$ and all $P \in S_{nd}$ are rational; $\mathcal N_{nd}$ consists of the $f \in F$ lying in `(Rx nd).integers`, in `R.integers`, and in the valuation subring of every $P \in S_{nd}$, and for such $f$ and such $P$ one has $P.\mathrm{evalAt}(f) \in A$; the crossing relation $c^x_{nd}\,c^y_{nd} = (\text{image of } \varpi'_{l_0})^{E_0}\,c^u_{nd}$ holds; $c^x_{nd}$ has vanishing $R_{nd}$-residue and its $R$-residue has $nd$-order $1$, while $c^y_{nd}$ has vanishing $R$-residue and its $R_{nd}$-residue has $b_{nd}$-order $1$ (each clause conditional on the relevant integrality); for $\tau$ in `A.inertiaSubgroupIn ℚ` with trivial tame character, the semilinear automorphism $g =$ [`ModularCurve.arithmeticGalois (xHFunctionField (q^2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54) preserves $S_{nd}$ and fixes $c^x_{nd}$ and $c^y_{nd}$; every $f \in F$ is a ratio of two elements of $\mathcal N_{0,nd,l}$ for some $l$, and also satisfies $f\,b = \sum_i c_i\, a_i$ for some nonzero $b$ and $a_i$ in $\mathcal N_{0,nd,l_0}$ and $c_i \in \bar{\mathbb Q}$; and for every $l$: $\mathcal N_{0,nd,l_0} \subseteq \mathcal N_{0,nd,l} \subseteq \mathcal N_{nd}$; $P \in S_{nd}$ if and only if $\mathcal N_{0,nd,l}$ lies in the valuation subring of $P$ and every non-unit $f$ of $\mathcal N_{0,nd,l}$ has $P.\mathrm{evalAt}(f)$ in the maximal ideal of $A$; $C'_l$ maps into $\mathcal N_{0,nd,l}$; every $g \in \mathcal N_{0,nd,l}$ differs from the image of some $o \in C'_l$ by a non-unit; any family $c_i \in \bar{\mathbb Q}$ linearly independent over $C'_l$ satisfies: $\sum_i c_i\, a_i = 0$ with $a_i \in \mathcal N_{0,nd,l}$ forces all $a_i = 0$; $c^x_{nd}, c^y_{nd} \in \mathcal N_{0,nd,l}$ and $c^u_{nd}$ is a unit of $\mathcal N_{0,nd,l}$; and there are a ring homomorphism $\sigma$ from $W_l$ to the adic completion of $\mathcal N_{0,nd,l}$ at its maximal ideal and a ring isomorphism $\iota$ of that completion with the crossing model `UVCrossingModel (Wc l) (πW l ^ E l)` (the quotient of two-variable power series over $W_l$ by the crossing ideal) such that $\sigma(\pi_{W,l})$ is the image of $\varpi'_l$, $\iota(\sigma(o)) =$ `const` $(o)$ for $o \in W_l$, every image of an element of $C'_l$ is in the image of $\sigma$, and the two order-detection clauses hold: an $f \in \mathcal N_{0,nd,l}$ with nonzero $R_{nd}$-residue of $b_{nd}$-order $n$ satisfies $\iota(f) - \gamma\, V^n \in (\mathrm{const}(\pi_{W,l}), U)$ for some unit $\gamma$ of the crossing model, and an $f$ with nonzero $R$-residue of $nd$-order $n$ satisfies $\iota(f) - \gamma\, U^n \in (\mathrm{const}(\pi_{W,l}), V)$ for some unit $\gamma$. Furthermore the sets $S_{nd}$, $nd \in N$, are pairwise disjoint; every $P \in S_{nd}$ specialises over $s$ in the sense of (2); for every $\zeta'$ and $\gamma \in \Gamma_0(M')$ there is a map $\tau_N$ on places of $F_{ss}$ preserving $N$ with $(\mathrm{levelAutBar}\,\zeta'\,\gamma)\cdot P \in S_{nd}$ iff $P \in S_{\tau_N(nd)}$ and with the pullback of `(Rx nd).integers` along that automorphism equal to `(Rx (τN nd)).integers`; for $\tau$ in the subgroup generated by the level automorphisms and preserving `R.integers`, and $nd \in N$, the translate of $nd$ lies in $N$ and `smulDisc τ` sends $S_{nd}$ to $S$ of that translate; $S_{nd} = \mathrm{An}(nd).\mathrm{dom}$ for $nd \in N$; and the image in $F$ of every element of `R₀.integers` lies in `(Rx nd).integers`.
--
--   (4k) Drinfeld identification with inertia action: for every ring homomorphism $\iota : \mathbb F_{q^2} \to \kappa$, regarded as an algebra structure, and assuming [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, there is a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb F_{q^2}$ with $\#C_s = 2\,\cdot$ `placeWidthChar q M' s` such that for every $\zeta$ in `Idx q` there are $\eta \in \{1, q\}$ and a $\kappa$-algebra isomorphism $e$ of $F_{ss}$ with [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) satisfying: for $\gamma \in \Gamma_0(M')$, given that `levelAutBar q M' ζ γ⁻¹` preserves `R.integers` and $(\mathrm{redQ}\,q\,\gamma, 1) \in$ `hSubgroup q`, $e$ carries the induced residue automorphism to the action of $(\mathrm{redQ}\,q\,\gamma, 1)$ on the Drinfeld function field; and for every $\tau \in$ `A.inertiaSubgroupIn ℚ`, every unit $\alpha$ of $\mathbb F_{q^2}$ with $\iota(\alpha) =$ `A.tameCharacter π τ`, and every semilinear automorphism $g$ equal to [`ModularCurve.arithmeticGalois (xHFunctionField (q^2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54): $g$ preserves `R.integers`, and for any witness of this and any ring automorphism $\varphi$ of $F_{ss}$ with $R$-residue of $g \cdot f$ equal to $\varphi$ of the $R$-residue of $f$, for every $d \in (\mathbb Z/q)^\times$ whose image in $\mathbb F_{q^2}$ equals $\alpha^{q+1}$ and every witness that $(\mathrm{diagOneElem}\,q\,(d^\eta)^{-1}, \alpha^\eta) \in$ `hSubgroup q`, the isomorphism $e$ carries $\varphi$ to the action of $(\mathrm{diagOneElem}\,q\,(d^\eta)^{-1}, \alpha^\eta)$ on the Drinfeld function field.
--
--   Thus (4e) produces $C_s$ and $e$ after fixing an $\mathbb F_{q^2}$-algebra structure on $\kappa$ and a $\zeta$, while (4k) produces a single $C_s$ for all $\zeta$ and supplements the $\Gamma_0(M')$-equivariance with the description of the action of tame inertia through $\eta \in \{1,q\}$.
--
--   This is the $q = 3$ instance of the supersingular-reduction package for the modular curve $X_H$ of level $q^2M'$: a regular prolongation of $A$ whose special fibre $F_{ss}$ is identified, equivariantly for $\Gamma_0(M')$ and for tame inertia, with a quotient of the function field of the Drinfeld curve $xy^q - x^qy = 1$, together with $q+1$ node annuli carrying crossing presentations over complete discrete valuation rings and smooth-point charts covering the remaining residue discs; the rigid auxiliary level given by a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$ is carried as a hypothesis, as at $q = 2$. It is a weakening of [`ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_three_of_dvd), retaining the conjuncts needed by the consumers that assemble the semistable covering of $X_H(q^2M')$ and its local affinoid and node-frame descriptions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
