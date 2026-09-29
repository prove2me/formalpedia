-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/d73b1597-ff6b-54e5-94b9-63a6d6c8636f
-- title:
--   Supersingular Gauss prolongation at q=2: charts, node annuli, Drinfeld
-- statement:
--   Setting. Let $q$ be a prime with $q=2$ (kept symbolic through the hypothesis $hq2$), let $M'$ be a nonzero natural number with $q\nmid M'$, and let $\ell$ be a prime with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a non-unit of $A$; write $\kappa=\mathrm{ResidueField}\,A$. Let $F=$ `fieldBar q M'` $=$ `xHFunctionFieldBar (q^2*M') (levelH q M')`, the intermediate field of $\overline{\mathbb{Q}}((t))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the $q$-expansion function field of $\Gamma_H(q^2M')$, where $H=$ `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. Write `modularFunctionFieldC κ M'` for the intermediate field of $\kappa((t))$ generated over $\kappa$ by `jqModC κ` and its $M'$-th expansion, and $j\in$ `modularFunctionFieldBar M'` for the element given by the coefficientwise image `coeffEmb (AlgebraicClosure ℚ) jq` of the Laurent expansion of the $j$-function.
--
--   Hypotheses. A finset $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$ is given together with the hypothesis $hW$ that $W$ consists exactly of the supersingular places, i.e. of those $w$ that are rational (the map $\kappa\to w.\mathrm{ResidueField}$ is surjective), satisfy the predicate `IsAffineGeomPlace`, and have $w.\mathrm{evalAt}$ of the generator `jGeomGen κ M'` in `ssJSet q κ`. The hypothesis $hle$ is the inclusion `modularFunctionFieldBar M'` $\le F$ of intermediate fields. Further given is a constant reduction $R_0$ of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` — a valuation subring $R_0.\mathrm{integers}$, a surjective ring homomorphism $R_0.\mathrm{residue}$ to `modularFunctionFieldC κ M'` with kernel the maximal ideal, a map on places, and the compatibilities of the structure `ConstantReduction` (constants of $F$ in $R_0.\mathrm{integers}$ exactly those in $A$, constants reducing to their residues in $\kappa$, every nonzero element scalable into the integers with nonzero residue, preservation of degrees and of divisor push-forward) — subject to the hypothesis $hR_0$ that $R_0$ is the coefficientwise reduction: for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}((t))$ lies in `modularFunctionFieldBar M'`, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise residue of $y$. Finally a place $s\in W$ is fixed, and an element $\pi\in\overline{\mathbb{Q}}$ with $\pi^{q^2-1}=q$ and $\pi\in A$.
--
--   Conclusion. There exist a field $F_{ss}$, a $\kappa$-algebra structure on $F_{ss}$, and a regular prolongation $R$ of $A$ from $F$ to $F_{ss}$ (a valuation subring $R.\mathrm{integers}\subseteq F$ with a surjective ring homomorphism $R.\mathrm{residue}$ onto $F_{ss}$ whose kernel is the maximal ideal, containing exactly the constants from $A$, reducing constants to their residues in $\kappa$, and with every nonzero element of $F$ scalable by a constant into the integers with nonzero residue) such that the following hold.
--
--   (1) Some $t\in F_{ss}$ is transcendental over $\kappa$.
--
--   (2) ($R$ prolongs $R_0$ over $s$.) For every $f\in$ `modularFunctionFieldBar M'` with $f\in R_0.\mathrm{integers}$ such that $f$ is regular wherever $j$ is (for every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$, $0\le P.\mathrm{ord}\,j$ implies $0\le P.\mathrm{ord}\,f$), and such that $R_0.\mathrm{residue}\,f$ lies in the valuation subring of $s$: the image of $f$ in $F$ lies in $R.\mathrm{integers}$ and its $R$-residue is the image under $\kappa\to F_{ss}$ of $s.\mathrm{evalAt}(R_0.\mathrm{residue}\,f)$.
--
--   (3) For every $\zeta\in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma\in\Gamma_0(M')$, the comap of $R.\mathrm{integers}$ along `levelAutBar q M' ζ γ` equals $R.\mathrm{integers}$.
--
--   Moreover there exist a finset $N$ of places of $F_{ss}$ over $\kappa$, subrings $S_Q\subseteq F$, ring homomorphisms $\varphi_Q\colon A[X]\to S_Q$ and $\chi_{0,Q}\colon S_Q\to\kappa$, and sets $D_Q$ of places of $F$ over $\overline{\mathbb{Q}}$, indexed by the places $Q$ of $F_{ss}$, with $\#N=q+1$ and the following properties.
--
--   (4) (Smooth-point charts.) For every $Q\notin N$: the image in $F$ of every $a\in A$ lies in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C\,a)$ is the image of $a$ in $F$ for all $a\in A$; $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$ in $\kappa$; $\chi_{0,Q}(\varphi_Q X)=0$; for every $c\in A$ with zero residue there is exactly one ring homomorphism $\chi\colon S_Q\to A$ with $\chi(\varphi_Q(C\,a))=a$ for all $a\in A$, with residue of $\chi(f)$ equal to $\chi_{0,Q}(f)$ for all $f$, and with $\chi(\varphi_Q X)=c$; every $f\in S_Q$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$, and the residue of the latter at $Q$ is the image of $\chi_{0,Q}(f)$ under $\kappa\to Q.\mathrm{ResidueField}$; the $R$-residue of $\varphi_Q X$ has $\mathrm{ord}_Q$ equal to $1$; $D_Q$ consists exactly of those places $P$ of $F$ over $\overline{\mathbb{Q}}$ that are rational, satisfy $f\in P.\mathrm{toValuationSubring}$ and $P.\mathrm{evalAt}\,f\in A$ for all $f\in S_Q$, and satisfy $A.\mathrm{valuation}(P.\mathrm{evalAt}\,f)<1\iff\chi_{0,Q}(f)=0$ for all $f\in S_Q$; every $A$-point $\chi\colon S_Q\to A$ fixing $A$ through $\varphi_Q\circ C$ and reducing to $\chi_{0,Q}$ is realised by a unique $P\in D_Q$ with $P.\mathrm{evalAt}\,f=\chi(f)$ for all $f\in S_Q$; for $P\in D_Q$, the valuation subring of $P$ consists exactly of the $f\in F$ for which there are $g,h\in S_Q$ with $P.\mathrm{evalAt}\,h\ne 0$ and $fh=g$; every nonzero $f\in F$ with $P.\mathrm{ord}\,f=0$ for all $P\in D_Q$ satisfies $cf=u$ for some nonzero $c\in\overline{\mathbb{Q}}$ and some unit $u$ of $S_Q$; and every $f\in R.\mathrm{integers}$ lying in the valuation subring of each $P\in D_Q$ lies in $S_Q$.
--
--   (5) (Disjointness.) If $Q,Q'\notin N$ and some $P$ lies in both $D_Q$ and $D_{Q'}$ then $Q=Q'$.
--
--   (6) (No cusps in the charts.) For $Q\notin N$ and $P\in D_Q$, $0\le P.\mathrm{ord}$ of the image of $j$ in $F$.
--
--   (7) (Level equivariance.) For every $\tau$ in the subgroup of $\overline{\mathbb{Q}}$-automorphisms of $F$ generated by the `levelAutBar q M' ζ γ` with $\zeta\in$ `Idx q` and $\gamma\in\Gamma_0(M')$, and every witness $h\tau$ that $\tau$ preserves $R.\mathrm{integers}$: for every place $Q$ of $F_{ss}$ one has $R.\mathrm{resAut}\,\tau\,h\tau\cdot Q\in N\iff Q\in N$, and if $Q\notin N$ then `smulDisc` $\tau\,D_Q=D_{R.\mathrm{resAut}\,\tau\,h\tau\cdot Q}$.
--
--   (8) (Drinfeld identification.) For every algebra structure $\mathbb{F}_{q^2}=$ `GaloisField q 2` $\to\kappa$, every proof that [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, and every $\zeta\in$ `Idx q`, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and a $\kappa$-algebra isomorphism $e$ from $F_{ss}$ onto [`DrinfeldCurve.quotField q κ C_s`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) (the fixed field in the Drinfeld function field of the subgroup generated by the actions of the elements $(1,\zeta')$, $\zeta'\in C_s$) such that $\#C_s=$ `placeWidthChar q M' s` and, for every $\gamma\in\Gamma_0(M')$ (with a witness that `levelAutBar q M' ζ γ⁻¹` preserves $R.\mathrm{integers}$ and a witness that $(\mathrm{red}_q\gamma,1)\in$ [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276)), the isomorphism $e$ carries $R.\mathrm{resAut}$ of `levelAutBar q M' ζ γ⁻¹` to the action of $(\mathrm{red}_q\gamma,1)$ on the Drinfeld function field.
--
--   (9) (Semilinear transport.) For every semilinear automorphism $g$ of $F$ over $\overline{\mathbb{Q}}$ (a compatible pair consisting of a ring automorphism of $F$ and one of $\overline{\mathbb{Q}}$) whose base automorphism preserves $A$, which preserves $R.\mathrm{integers}$ and fixes the image of $j$ in $F$, for every ring automorphism $\psi$ of $\kappa$ induced by $g$ on residues, and every ring automorphism $\varphi$ of $F_{ss}$ with $R.\mathrm{residue}(g\cdot f)=\varphi(R.\mathrm{residue}\,f)$ for all $f\in R.\mathrm{integers}$: if $Q\notin N$ and $Q'$ is the $\varphi$-transport of $Q$ (membership in the valuation subring of $Q'$ being membership of $\varphi^{-1}(y)$ in that of $Q$), then $Q'\notin N$, $f\in S_Q\iff g\cdot f\in S_{Q'}$, $\chi_{0,Q'}(g\cdot f)=\psi(\chi_{0,Q}(f))$ for $f\in S_Q$, and $P\in D_Q\iff g\cdot P\in D_{Q'}$.
--
--   (10) (Transitivity on $N$, and mobility off $N$.) For all $x,x'\in N$ there are $\zeta\in$ `Idx q` and $\gamma\in\Gamma_0(M')$ (with a witness that `levelAutBar q M' ζ γ` preserves $R.\mathrm{integers}$) with $R.\mathrm{resAut}$ of that automorphism sending $x$ to $x'$; and for every $Q\notin N$ there are such $\zeta,\gamma$ with $R.\mathrm{resAut}$ of `levelAutBar q M' ζ γ` moving $Q$.
--
--   (11) (Generators.) There are $n\in\mathbb{N}$ and $g_0,\dots,g_{n-1}\in R.\mathrm{integers}$ such that for every $i$, every $Q\notin N$ and every $P\in D_Q$ one has $g_i\in P.\mathrm{toValuationSubring}$ and $P.\mathrm{evalAt}\,g_i\in A$, and such that every $f\in F_{ss}$ lying in the valuation subring of every $Q\notin N$ belongs to the $\kappa$-subalgebra of $F_{ss}$ generated by the residues $R.\mathrm{residue}\,g_i$.
--
--   (12) (Node annuli.) There is an assignment $x\mapsto \mathrm{An}\,x$ of an `Annulus` over $A$ in $F$ (a set of places $\mathrm{dom}$, a parameter, and a modulus in the maximal ideal of $A$, subject to the axioms of that structure: the places of $\mathrm{dom}$ are rational, the parameter has value in the maximal ideal with modulus a multiple of it, each admissible value of the parameter is attained at exactly one place of $\mathrm{dom}$, $P.\mathrm{ord}$ of the parameter minus its value is $1$, and the unit principle holds) to every place $x$ of $F_{ss}$, such that:
--
--   — for each $x\in N$: the parameter lies in $R.\mathrm{integers}$, the $\mathrm{ord}_x$ of its $R$-residue is $1$, and for every $f\in R.\mathrm{integers}$ with nonzero $R$-residue and with $P.\mathrm{ord}\,f=0$ for all $P\in(\mathrm{An}\,x).\mathrm{dom}$, one has for each such $P$ that $P.\mathrm{evalAt}\,f\cdot(P.\mathrm{evalAt}\,\text{param})^{-\mathrm{ord}_x(R.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there (the cross-unit clause); the modulus of $\mathrm{An}\,x$ is nonzero in $\overline{\mathbb{Q}}$; no place of $(\mathrm{An}\,x).\mathrm{dom}$ lies in $D_Q$ for any $Q\notin N$; and every $P\in(\mathrm{An}\,x).\mathrm{dom}$ specialises to $s$, meaning: for every $f\in R_0.\mathrm{integers}$ in `modularFunctionFieldBar M'` that is regular wherever $j$ is and whose $R_0$-residue lies in the valuation subring of $s$, and every $a\in A$ whose residue equals $s.\mathrm{evalAt}(R_0.\mathrm{residue}\,f)$, the difference $P.\mathrm{evalAt}(\text{image of }f) - a$ lies in $A$ and in its maximal ideal;
--
--   — the domains of $\mathrm{An}\,x$ for distinct $x\in N$ are disjoint;
--
--   — for $\tau$ in the subgroup generated by the level automorphisms `levelAutBar q M' ζ γ` ($\gamma\in\Gamma_0(M')$) preserving $R.\mathrm{integers}$, and $x\in N$: `smulDisc` $\tau\,(\mathrm{An}\,x).\mathrm{dom}=(\mathrm{An}(R.\mathrm{resAut}\,\tau\,h\tau\cdot x)).\mathrm{dom}$;
--
--   — (covering) every rational place $P$ of $F$ over $\overline{\mathbb{Q}}$ that specialises to $s$ in the above sense lies either in $D_Q$ for some $Q\notin N$ or in $(\mathrm{An}\,x).\mathrm{dom}$ for some $x\in N$;
--
--   — (separation of ends) for distinct $x,x'\in N$ there is $g\in R.\mathrm{integers}$ with nonzero $R$-residue, with $\mathrm{ord}_x$ of that residue nonzero, with $P.\mathrm{ord}\,g=0$ for all $P\in(\mathrm{An}\,x).\mathrm{dom}$, and with $g$ in the valuation subring of every $P\in(\mathrm{An}\,x').\mathrm{dom}$, $P.\mathrm{evalAt}\,g$ being a unit of $A$;
--
--   — (node presentations) there exist: for each place $x$ of $F_{ss}$ a field $F_{I,x}$ with a $\kappa$-algebra structure, a regular prolongation $R_x$ of $A$ from $F$ to $F_{I,x}$ and a place $b_x$ of $F_{I,x}$ over $\kappa$; an index type $\Lambda$ with subrings $C'_l\subseteq\overline{\mathbb{Q}}$ contained in $A$, each a domain and a discrete valuation ring, elements $\varpi'_l\in C'_l$, a distinguished $l_0\in\Lambda$; complete discrete valuation rings $W_l$ (commutative domains, adically complete for their maximal ideals) with elements $\pi_{W,l}$, exponents $E(l)\in\mathbb{N}$ and $E_0\in\mathbb{N}$; sets $S_{nd}$ of places of $F$, subrings $\mathcal{N}_{nd}\subseteq F$ and $\mathcal{N}_{0,nd,l}\subseteq F$ with local-ring and Noetherian witnesses, and elements $c_{x,nd},c_{y,nd},c_{u,nd}\in F$, such that: for $d\in C'_l$ the residue of $d$ in $\kappa$ vanishes iff $d\in\varpi'_lC'_l$; $C'_{l_0}\subseteq C'_l$ for all $l$; $\varpi'_{l_0}\ne 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_{W,l}$ is irreducible and $E(l)\ge 1$; every $\tau$ in `A.inertiaSubgroupIn ℚ` with `A.tameCharacter π τ` $=1$ fixes $\varpi'_{l_0}$; and $(\varpi'_{l_0})^{E_0}=v\pi^w$ in $A$ for some $w\ge 1$ and some unit $v$ of $A$. Furthermore, for each $nd\in N$: $b_{nd}$, $nd$ and all places in $S_{nd}$ are rational; $\mathcal{N}_{nd}$ consists exactly of those $f\in F$ lying in $R_{nd}.\mathrm{integers}$, in $R.\mathrm{integers}$ and in the valuation subring of every $P\in S_{nd}$, and $P.\mathrm{evalAt}\,f\in A$ for $f\in\mathcal{N}_{nd}$ and $P\in S_{nd}$; $c_{x,nd}c_{y,nd}=(\varpi'_{l_0})^{E_0}c_{u,nd}$ in $F$; the $R_{nd}$-residue of $c_{x,nd}$ is $0$ while $\mathrm{ord}_{nd}$ of its $R$-residue is $1$, and the $R$-residue of $c_{y,nd}$ is $0$ while $\mathrm{ord}_{b_{nd}}$ of its $R_{nd}$-residue is $1$ (each asserted under the corresponding integrality witness); for $\tau$ in `A.inertiaSubgroupIn ℚ` with trivial tame character, the semilinear automorphism $g=$ `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ` preserves $S_{nd}$ and fixes $c_{x,nd}$ and $c_{y,nd}$; every $f\in F$ is a quotient $a/b$ with $a,b\in\mathcal{N}_{0,nd,l}$, $b\ne 0$, for some $l$, and also satisfies $fb=\sum_i c_i a_i$ for some $b\ne0$ and $a_i$ in $\mathcal{N}_{0,nd,l_0}$ and $c_i\in\overline{\mathbb{Q}}$; and for each $l$: $\mathcal{N}_{0,nd,l_0}\subseteq\mathcal{N}_{0,nd,l}\subseteq\mathcal{N}_{nd}$; $S_{nd}$ is exactly the set of places $P$ with $\mathcal{N}_{0,nd,l}$ inside the valuation subring of $P$ and with $P.\mathrm{evalAt}\,f$ in the maximal ideal of $A$ for every non-unit $f$ of $\mathcal{N}_{0,nd,l}$; $C'_l$ maps into $\mathcal{N}_{0,nd,l}$; every $g\in\mathcal{N}_{0,nd,l}$ differs from some element of $C'_l$ by a non-unit; any family $c_i\in\overline{\mathbb{Q}}$ linearly independent over $C'_l$ with $\sum_i c_ia_i=0$, $a_i\in\mathcal{N}_{0,nd,l}$, forces all $a_i=0$; $c_{x,nd},c_{y,nd}\in\mathcal{N}_{0,nd,l}$ and $c_{u,nd}$ is a unit of $\mathcal{N}_{0,nd,l}$; and there are a ring homomorphism $\sigma$ from $W_l$ to the adic completion of $\mathcal{N}_{0,nd,l}$ at its maximal ideal and a ring isomorphism $\iota$ from that completion onto the crossing model `UVCrossingModel (W_l) (π_{W,l}^{E(l)})` $=W_l[[U,V]]/(UV-\pi_{W,l}^{E(l)})$, with: $\sigma(\pi_{W,l})$ the image of $\varpi'_l$ whenever the latter lies in $\mathcal{N}_{0,nd,l}$; $\iota\circ\sigma$ the constant embedding; every element of $C'_l$ whose image lies in $\mathcal{N}_{0,nd,l}$ in the image of $\sigma$; and, for $f\in\mathcal{N}_{0,nd,l}$ and $n\in\mathbb{N}$, if the $R_{nd}$-residue of $f$ is nonzero with $\mathrm{ord}_{b_{nd}}$ equal to $n$ then $\iota(f)-\gamma V^n$ lies in the ideal generated by the constant $\pi_{W,l}$ and $U$ for some unit $\gamma$ of the crossing model, and symmetrically, if the $R$-residue of $f$ is nonzero with $\mathrm{ord}_{nd}$ equal to $n$ then $\iota(f)-\gamma U^n$ lies in the ideal generated by the constant $\pi_{W,l}$ and $V$ for some unit $\gamma$. In addition: the sets $S_{nd}$ for distinct $nd\in N$ are disjoint; every $P\in S_{nd}$ specialises to $s$ in the sense above; for every $\zeta'\in$ `Idx q` and $\gamma\in\Gamma_0(M')$ there is a map $\tau_N$ on places of $F_{ss}$ with $\tau_N(nd)\in N$, with `levelAutBar q M' ζ' γ` $\cdot P\in S_{nd}\iff P\in S_{\tau_N(nd)}$, and with the comap of $R_{nd}.\mathrm{integers}$ along that automorphism equal to $R_{\tau_N(nd)}.\mathrm{integers}$; for $\tau$ in the subgroup generated by the level automorphisms and preserving $R.\mathrm{integers}$, and $nd\in N$, one has $R.\mathrm{resAut}\,\tau\,h\tau\cdot nd\in N$ and `smulDisc` $\tau\,S_{nd}=S_{R.\mathrm{resAut}\,\tau\,h\tau\cdot nd}$; $S_{nd}=(\mathrm{An}\,nd).\mathrm{dom}$ for $nd\in N$; and for $nd\in N$ the image in $F$ of every $f\in R_0.\mathrm{integers}$ lies in $R_{nd}.\mathrm{integers}$.
--
--   (13) (Drinfeld identification with inertia.) For every ring homomorphism $\iota\colon\mathbb{F}_{q^2}\to\kappa$, taken as the algebra structure, and every proof that [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, there is a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ with $\#C_s=$ `placeWidthChar q M' s` such that for every $\zeta\in$ `Idx q` there are $\eta\in\{1,q\}$ and a $\kappa$-algebra isomorphism $e$ from $F_{ss}$ onto [`DrinfeldCurve.quotField q κ C_s`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) for which: the $\Gamma_0(M')$-equivariance of (8) holds, namely $e$ carries $R.\mathrm{resAut}$ of `levelAutBar q M' ζ γ⁻¹` to the action of $(\mathrm{red}_q\gamma,1)$ for $\gamma\in\Gamma_0(M')$; and for every $\tau\in$ `A.inertiaSubgroupIn ℚ` and every $\alpha\in\mathbb{F}_{q^2}^\times$ with $\iota(\alpha)=$ `A.tameCharacter π τ`, and $g=$ `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ`, the automorphism $g$ preserves $R.\mathrm{integers}$, and for every ring automorphism $\varphi$ of $F_{ss}$ compatible with $g$ through $R.\mathrm{residue}$, every $d\in(\mathbb{Z}/q)^\times$ whose image in $\mathbb{F}_{q^2}$ equals $\alpha^{q+1}$, and every witness that $(\mathrm{diag}(1,(d^\eta)^{-1}),\alpha^\eta)$ lies in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), the isomorphism $e$ carries $\varphi$ to the action of $(\mathrm{diag}(1,(d^\eta)^{-1}),\alpha^\eta)$ on the Drinfeld function field.
--
--   This is the $q=2$ case, with an auxiliary prime $\ell\equiv 11\pmod{12}$ dividing $M'$ as a rigidifying hypothesis, of the description of a supersingular component of the semistable reduction of $X_H(q^2M')$ at a place of $\overline{\mathbb{Q}}$ above $q$: it produces the component's Gauss-type prolongation together with smooth-point charts, residue discs, node annuli with $uv=\varpi^{E_0}$ presentations, cross units, and the identification of the reduced function field with a quotient of the Drinfeld-curve function field, equivariant for $\Gamma_0(M')$ and for tame inertia. It is obtained by discarding some conjuncts of a stronger single-source statement and is used downstream in the assembly of semistable coverings and of the node and affinoid data for the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia_of_eq_two_of_dvd
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
