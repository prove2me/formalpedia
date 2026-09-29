-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_affineChart
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_affineChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/b28c6617-d3ae-5341-8ca0-349862d4cc87
-- title:
--   Supersingular regular prolongation: charts, node models, affine chart
-- statement:
--   Throughout, $\overline{\mathbb{Q}}$ denotes `AlgebraicClosure ℚ`; for a valuation subring $A$ of $\overline{\mathbb{Q}}$ write $\kappa$ for its residue field. The data are: a prime $q$ with $5\le q$, a nonzero natural number $M'$ with $q\nmid M'$, a valuation subring $A\subseteq\overline{\mathbb{Q}}$ with `A.LiesOverPrime q` (i.e. $q$ is a non-unit of $A$), a finite set $W$ of places of $F_\kappa:=$ `modularFunctionFieldC κ M'` over $\kappa$ with `hW` saying that $W$ is exactly `ssPlaces q M' κ`, that is, the set of places $w$ that are rational (the structure map $\kappa\to w.\mathrm{ResidueField}$ is onto), satisfy the predicate `IsAffineGeomPlace` and have $w.\mathrm{evalAt}$ of `jGeomGen κ M'` in `ssJSet q κ`; an inclusion `hle` of $\bar F_0:=$ `modularFunctionFieldBar M'` (the $\overline{\mathbb{Q}}$-base change, inside Laurent series over $\overline{\mathbb{Q}}$, of the full level-$M'$ modular function field) into $\bar F:=$ `fieldBar q M'` $=$ `xHFunctionFieldBar (q^2*M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^{\times}\to(\mathbb{Z}/q)^{\times}$, i.e. the units congruent to $1$ modulo $q$; a constant reduction $R_0$ of type `ConstantReduction A ↥(modularFunctionFieldBar M') F_κ`, consisting of a valuation subring $R_0.\mathrm{integers}$ of $\bar F_0$, a surjective ring map $R_0.\mathrm{residue}$ onto $F_\kappa$ whose kernel is the maximal ideal, a map on places preserving degrees and pushing divisors forward to orders, the condition that a constant of $\overline{\mathbb{Q}}$ is integral exactly when it lies in $A$ and reduces to its residue, and the rescaling property that every nonzero $f$ has a constant multiple integral with nonzero residue; the hypothesis `hR₀`, that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}$ lies in $\bar F_0$, that element is $R_0$-integral and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$; an element $s$ of $W$, regarded as a place of $F_\kappa$; and an element $\pi_t\in\overline{\mathbb{Q}}$ with $\pi_t^{q^2-1}=q$ and $\pi_t\in A$.
--
--   Write $\mathbf{j}\in\bar F_0$ for the element given by the coefficientwise image of the $q$-expansion `jq` of $j$, and say that $f\in\bar F_0$ is *$j$-regular* if $0\le P.\mathrm{ord}(f)$ for every place $P$ of $\bar F_0$ over $\overline{\mathbb{Q}}$ with $0\le P.\mathrm{ord}(\mathbf{j})$.
--
--   The assertion is the existence of a field $F_{SS}$, a $\kappa$-algebra structure on it, and a regular prolongation $R$ of type `RegularProlongation A (fieldBar q M') FSS` — a valuation subring $R.\mathrm{integers}$ of $\bar F$ together with a surjective ring map $R.\mathrm{residue}$ onto $F_{SS}$ whose kernel is the maximal ideal, with constants integral exactly on $A$ and reducing to their $A$-residues, and with the rescaling property — such that the following hold.
--
--   (i) Some element of $F_{SS}$ is transcendental over $\kappa$.
--
--   (ii) ($R$ lies over $s$.) For every $f\in R_0.\mathrm{integers}$ that is $j$-regular and whose reduction $R_0.\mathrm{residue}(f)$ lies in the valuation subring of $s$, the image of $f$ in $\bar F$ under `IntermediateField.inclusion hle` is $R$-integral and its $R$-residue is the image under $\kappa\to F_{SS}$ of $s.\mathrm{evalAt}(R_0.\mathrm{residue}(f))$.
--
--   (iii) (Level invariance.) For every $\zeta\in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma\in SL_2(\mathbb{Z})$ lying in $\Gamma_0(M')$, the pullback of $R.\mathrm{integers}$ along `levelAutBar q M' ζ γ` is $R.\mathrm{integers}$.
--
--   (iv) There are a finite set $N$ of places of $F_{SS}$ over $\kappa$ with $\#N=q+1$, and assignments $Q\mapsto S_x(Q)$ (a subring of $\bar F$), $Q\mapsto \varphi_x(Q)\colon A[X]\to S_x(Q)$, $Q\mapsto \chi_{0,x}(Q)\colon S_x(Q)\to\kappa$ and $Q\mapsto D_x(Q)$ (a set of places of $\bar F$ over $\overline{\mathbb{Q}}$), such that for every place $Q\notin N$: the image of $A$ lies in $S_x(Q)$; $\varphi_x(Q)$ is formally smooth and formally unramified; $\varphi_x(Q)(C\,a)$ is the image of $a$ for all $a\in A$, and $\chi_{0,x}(Q)(\varphi_x(Q)(C\,a))$ is the residue of $a$, while $\chi_{0,x}(Q)(\varphi_x(Q)(X))=0$; for every $c\in A$ of residue $0$ there is a unique ring map $\chi\colon S_x(Q)\to A$ with $\chi(\varphi_x(Q)(C\,a))=a$ for all $a$, with $\chi$ lifting $\chi_{0,x}(Q)$ (the $A$-residue of $\chi(f)$ is $\chi_{0,x}(Q)(f)$), and with $\chi(\varphi_x(Q)(X))=c$; every $f\in S_x(Q)$ is $R$-integral, its $R$-residue lies in the valuation subring of $Q$ and its image in $Q.\mathrm{ResidueField}$ is the image of $\chi_{0,x}(Q)(f)$; $\varphi_x(Q)(X)$ is $R$-integral with $Q.\mathrm{ord}$ of its residue equal to $1$; $D_x(Q)$ consists exactly of the rational places $P$ such that every $f\in S_x(Q)$ is $P$-integral with $P.\mathrm{evalAt}(f)\in A$, and such that $A.\mathrm{valuation}(P.\mathrm{evalAt}(f))<1$ holds precisely when $\chi_{0,x}(Q)(f)=0$; every ring map $\chi\colon S_x(Q)\to A$ fixing the constants and lifting $\chi_{0,x}(Q)$ comes from a unique $P\in D_x(Q)$, in the sense that $P.\mathrm{evalAt}(f)=\chi(f)$ for all $f$; for $P\in D_x(Q)$ the valuation subring of $P$ is the localisation of $S_x(Q)$ described by: $f$ is $P$-integral iff $f\cdot h=g$ for some $g,h\in S_x(Q)$ with $P.\mathrm{evalAt}(h)\neq0$; every nonzero $f\in\bar F$ with $P.\mathrm{ord}(f)=0$ for all $P\in D_x(Q)$ satisfies $c\cdot f=u$ for some $c\in\overline{\mathbb{Q}}^{\times}$ and some unit $u$ of $S_x(Q)$; and every $R$-integral $f$ that is $P$-integral for all $P\in D_x(Q)$ lies in $S_x(Q)$.
--
--   Moreover: for $Q,Q'\notin N$, a place $P$ lying in both $D_x(Q)$ and $D_x(Q')$ forces $Q=Q'$; for $Q\notin N$ and $P\in D_x(Q)$ one has $0\le P.\mathrm{ord}$ of the image of $\mathbf{j}$ in $\bar F$; and for every $\tau$ in the subgroup of $\mathrm{Aut}_{\overline{\mathbb{Q}}}(\bar F)$ generated by the automorphisms `levelAutBar q M' ζ γ` ($\zeta\in$ `Idx q`, $\gamma\in\Gamma_0(M')$) and every witness $h\tau$ that $\tau$ preserves $R.\mathrm{integers}$: the induced residue automorphism `R.resAut τ hτ` carries $N$ to $N$ (membership is equivalent before and after), and for $Q\notin N$ one has `smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q)`, where `smulDisc τ D = {P | τ⁻¹ • P ∈ D}`.
--
--   (v) (Drinfeld description, first form.) For every $\mathbb{F}_{q^2}$-algebra structure on $\kappa$, every witness that [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain and every $\zeta\in$ `Idx q`, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and a $\kappa$-algebra isomorphism $e$ from $F_{SS}$ onto [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) (the fixed field, inside the fraction field of `CoordRing q κ`, of the subgroup generated by the actions of the elements $(1,\zeta')$ with $\zeta'\in C_s$) with $\mathrm{card}\,C_s=2\cdot$ `placeWidthChar q M' s`, and such that for every $\gamma\in\Gamma_0(M')$, given that `levelAutBar q M' ζ γ⁻¹` preserves $R.\mathrm{integers}$ and that $(\mathrm{redQ}_q(\gamma),1)$ lies in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) (the kernel of $(\mathbf{g},u)\mapsto\det(\mathbf{g})\cdot u^{q+1}$ on $GL_2(\mathbb{Z}/q)\times\mathbb{F}_{q^2}^{\times}$), conjugation by $e$ turns the residue automorphism of `levelAutBar q M' ζ γ⁻¹` into [`DrinfeldCurve.hFunctionFieldAction q κ`](def/DrinfeldCurve_FunctionField.html#L16) applied to that element, pointwise on $F_{SS}$.
--
--   (vi) (Drinfeld description with inertia.) For every ring map $\iota\colon\mathbb{F}_{q^2}\to\kappa$, with the induced algebra structure, and every witness that `CoordRing q κ` is a domain, there is a subgroup $C_s$ with $\mathrm{card}\,C_s=2\cdot$ `placeWidthChar q M' s` such that for every $\zeta\in$ `Idx q` there is a $\kappa$-algebra isomorphism $e$ from $F_{SS}$ onto `quotField q κ Cs` satisfying the $\Gamma_0(M')$-equivariance of (v), and in addition the following inertia compatibility: for every $\tau$ in `A.inertiaSubgroupIn ℚ` (the image of the inertia subgroup of $A$ inside its decomposition subgroup in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$) and every $\alpha\in\mathbb{F}_{q^2}^{\times}$ with $\iota(\alpha)=$ `A.tameCharacter πt τ` (the $A$-residue of $\tau(\pi_t)/\pi_t$), and every semilinear automorphism $g$ of $\bar F$ over $\overline{\mathbb{Q}}$ equal to [`ModularCurve.arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54) (coefficientwise action of $\tau$ on Laurent series): $g$ preserves $R.\mathrm{integers}$, and for every such preservation witness, every ring automorphism $\varphi$ of $F_{SS}$ compatible with $g$ through $R.\mathrm{residue}$, every $d\in(\mathbb{Z}/q)^{\times}$ whose image in $\mathbb{F}_{q^2}$ is $\alpha^{q+1}$, and every witness that $(\mathrm{diagOneElem}_q((d^q)^{-1}),\alpha^q)$ lies in `hSubgroup q`, conjugation by $e$ turns $\varphi$ into `hFunctionFieldAction q κ` applied to that element, pointwise.
--
--   (vii) (Affine chart.) There is a subring $B$ of $\bar F$ containing the image of $A$, contained in $R.\mathrm{integers}$, contained in $S_x(Q)$ for every $Q\notin N$, and such that every $z\in F_{SS}$ lying in the valuation subring of every $Q\notin N$ is the $R$-residue of some $f\in B$.
--
--   (viii) (Nodes.) There is a finite set $N'$ of places of $F_{SS}$ over $\kappa$ with $\#N'=q+1$, together with: for each place $x$ of $F_{SS}$ a field $FI_x(x)$ with a $\kappa$-algebra structure, a regular prolongation $R_x(x)$ of type `RegularProlongation A (fieldBar q M') (FIx x)` and a place $b_x(x)$ of $FI_x(x)$ over $\kappa$; an index type $\Lambda$, subrings $C'(l)\subseteq\overline{\mathbb{Q}}$ all contained in $A$ (hypothesis `hC'A`), each a domain and a discrete valuation ring, elements $\varpi'(l)\in C'(l)$ and a base index $l_0$; commutative rings $W_c(l)$, each a domain, a discrete valuation ring and adically complete for its maximal ideal, elements $\pi(l)\in W_c(l)$, natural numbers $E(l)$ and $E_0$; and, for each place $nd$ of $F_{SS}$, a set $S(nd)$ of places of $\bar F$ over $\overline{\mathbb{Q}}$, subrings $\mathcal{N}(nd)$ and $\mathcal{N}_0(nd,l)$ of $\bar F$, the latter local (`hloc`) and Noetherian (`hnoe`), and elements $c_x(nd),c_y(nd),c_u(nd)\in\bar F$.
--
--   These satisfy, first, the constant-field clauses: for each $l$, an element $d\in C'(l)$ has $A$-residue $0$ exactly when $d\in\varpi'(l)\,C'(l)$; $C'(l_0)\le C'(l)$ for all $l$; $\varpi'(l_0)\neq0$; every element of $A$ is algebraic over $C'(l_0)$; each $\pi(l)$ is irreducible and $1\le E(l)$; every $\tau\in$ `A.inertiaSubgroupIn ℚ` with `A.tameCharacter πt τ = 1` fixes $\varpi'(l_0)$; and there are $w\ge1$ and a unit $v$ of $A$ with $\varpi'(l_0)^{E_0}=v\,\pi_t^{\,w}$ in $A$.
--
--   Second, for every $nd\in N'$: $b_x(nd)$, $nd$ and every $P\in S(nd)$ are rational places; $\mathcal{N}(nd)$ consists exactly of the $f\in\bar F$ that are $R_x(nd)$-integral, $R$-integral and $P$-integral for every $P\in S(nd)$; for $f\in\mathcal{N}(nd)$ and $P\in S(nd)$ one has $P.\mathrm{evalAt}(f)\in A$; $c_x(nd)\,c_y(nd)=\varpi'(l_0)^{E_0}\,c_u(nd)$ (images in $\bar F$); if $c_x(nd)$ is $R_x(nd)$-integral its $R_x(nd)$-residue is $0$, if it is $R$-integral then $nd.\mathrm{ord}$ of its $R$-residue is $1$; if $c_y(nd)$ is $R$-integral its $R$-residue is $0$, and if it is $R_x(nd)$-integral then $b_x(nd).\mathrm{ord}$ of its $R_x(nd)$-residue is $1$; for every $\tau\in$ `A.inertiaSubgroupIn ℚ` with trivial tame character, the semilinear automorphism $g$ given by `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ` preserves $S(nd)$ (membership of $P$ and of $g\cdot P$ are equivalent) and fixes $c_x(nd)$ and $c_y(nd)$; every $f\in\bar F$ is a quotient $a/b$ with $a,b\in\mathcal{N}_0(nd,l)$, $b\neq0$, for some $l$; and every $f\in\bar F$ satisfies $f\cdot b=\sum_i c_i\,a_i$ for some finite family of scalars $c_i\in\overline{\mathbb{Q}}$ and elements $a_i,b\in\mathcal{N}_0(nd,l_0)$ with $b\neq0$.
--
--   Furthermore, for every $l$: $\mathcal{N}_0(nd,l_0)\le\mathcal{N}_0(nd,l)\le\mathcal{N}(nd)$; a place $P$ lies in $S(nd)$ exactly when every element of $\mathcal{N}_0(nd,l)$ is $P$-integral and every non-unit $f$ of $\mathcal{N}_0(nd,l)$ has $P.\mathrm{evalAt}(f)$ in $A$ and in its maximal ideal; the image of $C'(l)$ lies in $\mathcal{N}_0(nd,l)$; every $g\in\mathcal{N}_0(nd,l)$ differs from the image of some $o\in C'(l)$ by a non-unit; if scalars $c_i\in\overline{\mathbb{Q}}$ are linearly independent over $C'(l)$ and $\sum_i c_i\,a_i=0$ with $a_i\in\mathcal{N}_0(nd,l)$, then all $a_i=0$; there is a subring $B_x$ of $\bar F$ contained in $\mathcal{N}_0(nd,l)$ and containing $c_x(nd)$, $c_y(nd)$, $c_u(nd)$, such that $\mathcal{N}_0(nd,l)$ is obtained from $B_x$ by inverting those elements of $B_x$ that are units of $\mathcal{N}_0(nd,l)$ ($f\in\mathcal{N}_0(nd,l)$ iff $f\cdot h=g$ with $g,h\in B_x$ and $h$ a unit whenever it lies in $\mathcal{N}_0(nd,l)$), and such that $B_x$ is generated by the image of $C'(l)$ together with a finite set $T$; $c_x(nd),c_y(nd)\in\mathcal{N}_0(nd,l)$ and $c_u(nd)$ is a unit there; and there are a ring map $\sigma$ from $W_c(l)$ to the adic completion of $\mathcal{N}_0(nd,l)$ at its maximal ideal and a ring isomorphism $\iota$ from that completion onto `UVCrossingModel (Wc l) (π l ^ E l)`, the quotient of $W_c(l)[[X_0,X_1]]$ by $X_0X_1-\pi(l)^{E(l)}$, such that $\sigma(\pi(l))$ is the image of $\varpi'(l)$ whenever the latter lies in $\mathcal{N}_0(nd,l)$; $\iota(\sigma(o))=$ `const (π l ^ E l) o` for all $o\in W_c(l)$; every element of $C'(l)$ whose image lies in $\mathcal{N}_0(nd,l)$ is $\sigma(o)$ for some $o$; and the two order-matching clauses: for $f\in\mathcal{N}_0(nd,l)$ and $n\in\mathbb{N}$, if the $R_x(nd)$-residue of $f$ is nonzero with $b_x(nd).\mathrm{ord}=n$, then $\iota(f)-\gamma\cdot V^n$ lies in the ideal generated by `const (π l ^ E l) (π l)` and $U$ for some unit $\gamma$ of the crossing model, and symmetrically, if the $R$-residue of $f$ is nonzero with $nd.\mathrm{ord}=n$, then $\iota(f)-\gamma\cdot U^n$ lies in the ideal generated by `const (π l ^ E l) (π l)` and $V$ for some unit $\gamma$, where $U$ and $V$ denote the distinguished elements `U (π l ^ E l)` and `V (π l ^ E l)`.
--
--   Finally, the following global clauses hold. The sets $S(nd)$, $nd\in N'$, are pairwise disjoint. For $nd\in N'$, $P\in S(nd)$, every $j$-regular $f\in R_0.\mathrm{integers}$ whose reduction lies in the valuation subring of $s$, and every $a\in A$ whose residue is $s.\mathrm{evalAt}(R_0.\mathrm{residue}(f))$, the difference $P.\mathrm{evalAt}(f)-a$ lies in $A$ and in its maximal ideal. For every $\zeta'\in$ `Idx q` and $\gamma\in\Gamma_0(M')$ there is a map $\tau_N$ on places of $F_{SS}$ such that every $nd\in N'$ has $\tau_N(nd)\in N'$, with $(\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma)\cdot P\in S(nd)$ equivalent to $P\in S(\tau_N(nd))$, and with the pullback of $R_x(nd).\mathrm{integers}$ along that automorphism equal to $R_x(\tau_N(nd)).\mathrm{integers}$. For every $\tau$ in the subgroup generated by the level automorphisms and every witness that $\tau$ preserves $R.\mathrm{integers}$, and every $nd\in N'$: `R.resAut τ hτ • nd` lies in $N'$ and `smulDisc τ (S nd) = S (R.resAut τ hτ • nd)`. For $nd\in N'$, every $f\in R_0.\mathrm{integers}$ has image $R_x(nd)$-integral; and there is a ring map $j_{nd}\colon F_\kappa\to FI_x(nd)$ such that for every $f\in R_0.\mathrm{integers}$ the image of $f$ is $R_x(nd)$-integral with $R_x(nd)$-residue $j_{nd}(R_0.\mathrm{residue}(f))$, and such that $g\in F_\kappa$ lies in the valuation subring of $s$ exactly when $j_{nd}(g)$ lies in that of $b_x(nd)$.
--
--   The Hasse datum: the Laurent series [`ModularCurve.jqNModC (AlgebraicClosure ℚ) q`](def/ModularCurve_JqCoeff.html#L18) (the $q$-fold expansion of the $j$-series) lies in $\bar F$, and there is $a_0\in A$ such that this element minus $a_0$ is $R$-integral with $R$-residue $0$, while the $q$-th power of the residue of $a_0$ equals $s.\mathrm{evalAt}$ of `jGeomGen κ M'`; moreover there is $c'\in\overline{\mathbb{Q}}$ such that $c'\cdot(j_{q}-a_0)$ is $R$-integral with nonzero residue and, for every $nd\in N'$, $j_{q}-a_0$ is $R_x(nd)$-integral with nonzero $R_x(nd)$-residue and $nd.\mathrm{ord}$ of the $R$-residue of $c'\cdot(j_q-a_0)$ equals $-\,b_x(nd).\mathrm{ord}$ of the $R_x(nd)$-residue of $j_q-a_0$, where $j_q$ abbreviates the above element of $\bar F$.
--
--   Separation: for every $x\in N'$ and every place $y\notin N'$ of $F_{SS}$ there is $g\in\bar F$ that is $R$-integral, lies in $\mathcal{N}_0(x,l_0)$ and is a non-unit there, has $y.\mathrm{ord}$ of its $R$-residue equal to $0$ and nonzero $R$-residue, and is $P$-integral for every rational place $P$ of $\bar F$ at which the image of $\mathbf{j}$ has non-negative order. For distinct $x,x'\in N'$ there is $g\in\bar F$ lying in $\mathcal{N}_0(x,l_0)$ and in $\mathcal{N}_0(x',l_0)$, equal to $c_x(x)$ times a unit of $\mathcal{N}_0(x,l_0)$, and a unit of $\mathcal{N}_0(x',l_0)$.
--
--   Covering: every rational place $P$ of $\bar F$ which specialises to $s$ — meaning that for every $j$-regular $f\in R_0.\mathrm{integers}$ whose reduction lies in the valuation subring of $s$ and every $a\in A$ whose residue is $s.\mathrm{evalAt}(R_0.\mathrm{residue}(f))$, the difference $P.\mathrm{evalAt}(f)-a$ lies in $A$ and in its maximal ideal — either lies in $S(nd)$ for some $nd\in N'$, or else lies in a set $D$ for which there are a place $Q\notin N'$ of $F_{SS}$ and $z\in\bar F$ with `R.IsResidueDisc Q D z`: that is, $z$ is a disc coordinate (each $P'\in D$ is rational with $z$ integral at $P'$ and $A.\mathrm{valuation}(P'.\mathrm{evalAt}(z))<1$; $z$ is $R$-integral with $Q.\mathrm{ord}$ of its residue equal to $1$; each $c$ of $A$-valuation $<1$ is $P'.\mathrm{evalAt}(z)$ for exactly one $P'\in D$; $P'.\mathrm{ord}(z-P'.\mathrm{evalAt}(z))=1$; and nonzero functions of order $0$ along $D$ have constant valuation there), $D$ is pointwise compatible with $Q$ (residues of functions integral along $D$ match the $Q$-residue of their $R$-residue), and the degree condition holds (for $R$-integral $f$ with nonzero residue, a divisor supported on $D$ and agreeing there with the orders of $f$ has total degree $Q.\mathrm{ord}(R.\mathrm{residue}(f))$).
--
--   This is the construction, at a supersingular point $s$ of the characteristic-$q$ modular curve of level $M'$, of the supersingular (Drinfeld) component of the special fibre of the modular curve of level $q^2M'$ with level group the units congruent to $1$ modulo $q$: a regular prolongation of the function field whose residue field is identified with a Drinfeld quotient field, equipped with its $q+1$ ends, smooth-point charts and $A$-discs off the ends, an affine chart of the component minus its ends, crossing ($uv=\pi^{E}$) presentations at the $q+1$ nodes, the Hasse datum relating $j$ and $j_q$, and the actions of $\Gamma_0(M')$ and of tame inertia. It is the producer for the further edition that adds crossing units and the Igusa structure over $S$, from which the local analysis of the special fibre at $q$ is drawn.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_affineChart.lean

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

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_affineChart
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

    (πt : AlgebraicClosure ℚ) (hπt : πt ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπA : πt ∈ A) :
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
                ι (α : GaloisField q 2) = A.tameCharacter πt τ →
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
                          DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧

        (∃ B : Subring ↥(fieldBar q M'),

          (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ B) ∧

          (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers) ∧

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sx Q) ∧

          (∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
            ∃ (f : ↥(fieldBar q M')) (_ : f ∈ B) (hfR : f ∈ R.integers), R.residue ⟨f, hfR⟩ = z)) ∧

        ∃ (N' : Finset (Place (ResidueField A) FSS)),

          N'.card = q + 1 ∧
        ∃
          (FIx : Place (ResidueField A) FSS → Type) (_ : ∀ x, Field (FIx x)) (_ : ∀ x, Algebra (ResidueField A) (FIx x))
          (Rx : ∀ x : Place (ResidueField A) FSS, RegularProlongation A (fieldBar q M') (FIx x))
          (bx : ∀ x : Place (ResidueField A) FSS, Place (ResidueField A) (FIx x))

          (Λ : Type) (C' : Λ → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : Λ) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
          (_ : ∀ l, IsDomain ↥(C' l)) (_ : ∀ l, IsDiscreteValuationRing ↥(C' l))
          (ϖ' : ∀ l, ↥(C' l)) (l₀ : Λ)
          (Wc : Λ → Type) (_ : ∀ l, CommRing (Wc l)) (_ : ∀ l, IsDomain (Wc l)) (_ : ∀ l, IsDiscreteValuationRing (Wc l))
          (_ : ∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l))
          (π : ∀ l, Wc l) (E : Λ → ℕ) (E₀ : ℕ)

          (S : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
          (𝒩 : Place (ResidueField A) FSS → Subring (fieldBar q M'))
          (𝒩₀ : Place (ResidueField A) FSS → Λ → Subring (fieldBar q M'))
          (hloc : ∀ nd l, IsLocalRing ↥(𝒩₀ nd l)) (hnoe : ∀ nd l, IsNoetherianRing ↥(𝒩₀ nd l))
          (cx cy cu : Place (ResidueField A) FSS → fieldBar q M'),

          (∀ (l : Λ) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d') ∧
          (∀ l, C' l₀ ≤ C' l) ∧
          ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ≠ 0 ∧
          (∀ a : AlgebraicClosure ℚ, a ∈ A → IsAlgebraic ↥(C' l₀) a) ∧
          (∀ l, Irreducible (π l)) ∧ (∀ l, 1 ≤ E l) ∧

          (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 →
            τ ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) = ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ)) ∧

          (∃ w : ℕ, 1 ≤ w ∧ ∃ v : (↥A)ˣ,
            (⟨((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ), hC'A l₀ _ (ϖ' l₀).2⟩ : ↥A) ^ E₀ = (v : ↥A) * ⟨πt, hπA⟩ ^ w) ∧

          (∀ nd ∈ N',

            (bx nd).IsRational ∧ nd.IsRational ∧ (∀ P ∈ S nd, P.IsRational) ∧

            (∀ f : fieldBar q M', f ∈ 𝒩 nd ↔ f ∈ (Rx nd).integers ∧ f ∈ R.integers ∧ ∀ P ∈ S nd, f ∈ P.toValuationSubring) ∧
            (∀ f ∈ 𝒩 nd, ∀ P ∈ S nd, P.evalAt f ∈ A) ∧

            cx nd * cy nd = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ * cu nd ∧
            (∀ h₁ : cx nd ∈ (Rx nd).integers, (Rx nd).residue ⟨cx nd, h₁⟩ = 0) ∧
            (∀ h₂ : cx nd ∈ R.integers, nd.ord (R.residue ⟨cx nd, h₂⟩) = 1) ∧
            (∀ h₂ : cy nd ∈ R.integers, R.residue ⟨cy nd, h₂⟩ = 0) ∧
            (∀ h₁ : cy nd ∈ (Rx nd).integers, (bx nd).ord ((Rx nd).residue ⟨cy nd, h₁⟩) = 1) ∧

            (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 →
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
                (ι : AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l) ≃+* UVCrossingModel (Wc l) (π l ^ E l)),
                (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l,
                  σ (π l) = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ o : Wc l, ι (σ o) = const (π l ^ E l) o) ∧
                (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l),
                  ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₁ : f.1 ∈ (Rx nd).integers), (Rx nd).residue ⟨f.1, h₁⟩ ≠ 0 →
                  (bx nd).ord ((Rx nd).residue ⟨f.1, h₁⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (π l ^ E l), IsUnit γ ∧
                      ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * V (π l ^ E l) ^ n ∈
                        Ideal.span {const (π l ^ E l) (π l), U (π l ^ E l)}) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
                  nd.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (π l ^ E l), IsUnit γ ∧
                      ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * U (π l ^ E l) ^ n ∈
                        Ideal.span {const (π l ^ E l) (π l), V (π l ^ E l)}))) ∧

          (∀ nd ∈ N', ∀ nd' ∈ N', ∀ P, P ∈ S nd → P ∈ S nd' → nd = nd') ∧

          (∀ nd ∈ N', ∀ P ∈ S nd, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
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
            ∀ nd ∈ N', τN nd ∈ N' ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), (levelAutBar q M' ζ' γ) • P ∈ S nd ↔ P ∈ S (τN nd)) ∧
              ((Rx nd).integers).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = (Rx (τN nd)).integers) ∧

          (∀ τ ∈ Subgroup.closure {τ : (fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] (fieldBar q M') |
                ∃ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ' γ},
            ∀ (hτ : ∀ f : fieldBar q M', τ f ∈ R.integers ↔ f ∈ R.integers), ∀ nd ∈ N',
              R.resAut τ hτ • nd ∈ N' ∧
              AlgebraicCurve.RegularProlongation.smulDisc τ (S nd) = S (R.resAut τ hτ • nd)) ∧

          (∀ nd ∈ N', ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ (Rx nd).integers) ∧

          (∀ nd ∈ N', ∃ j : modularFunctionFieldC (ResidueField A) M' →+* FIx nd,
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ (Rx nd).integers,
                (Rx nd).residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
            ∀ g : modularFunctionFieldC (ResidueField A) M',
              g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
                j g ∈ (bx nd).toValuationSubring) ∧

          (∃ (hJK : ModularCurve.jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M') (a₀ : AlgebraicClosure ℚ) (ha₀ : a₀ ∈ A)
             (hR : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀ ∈ R.integers),
            R.residue ⟨_, hR⟩ = 0 ∧
            (IsLocalRing.residue ↥A ⟨a₀, ha₀⟩) ^ q = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField ↥A) M') ∧
            ∃ (c' : AlgebraicClosure ℚ) (htc : c' • ((⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀) ∈ R.integers),
              R.residue ⟨_, htc⟩ ≠ 0 ∧
              ∀ nd ∈ N', ∃ hC : ((⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀) ∈ (Rx nd).integers,
                (Rx nd).residue ⟨_, hC⟩ ≠ 0 ∧
                nd.ord (R.residue ⟨_, htc⟩) = -((bx nd).ord ((Rx nd).residue ⟨_, hC⟩))) ∧

          (∀ x ∈ N', ∀ y : Place (ResidueField A) FSS, y ∉ N' →
                ∃ (g : ↥(fieldBar q M')) (hg : g ∈ R.integers) (hg₀ : g ∈ 𝒩₀ x l₀),
                  ¬ IsUnit (⟨g, hg₀⟩ : ↥(𝒩₀ x l₀)) ∧
                  y.ord (R.residue ⟨g, hg⟩) = 0 ∧ R.residue ⟨g, hg⟩ ≠ 0 ∧
                  ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
                    0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) → g ∈ P.toValuationSubring) ∧

          (∀ x ∈ N', ∀ x' ∈ N', x ≠ x' →
                ∃ (g : ↥(fieldBar q M')) (hgx : g ∈ 𝒩₀ x l₀) (hcx : cx x ∈ 𝒩₀ x l₀) (hgx' : g ∈ 𝒩₀ x' l₀),
                  (∃ u : (↥(𝒩₀ x l₀))ˣ, (⟨g, hgx⟩ : ↥(𝒩₀ x l₀)) = ⟨cx x, hcx⟩ * (u : ↥(𝒩₀ x l₀))) ∧
                  IsUnit (⟨g, hgx'⟩ : ↥(𝒩₀ x' l₀))) ∧

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
            (∃ nd, nd ∈ N' ∧ P ∈ S nd) ∨
            (∃ Q : Place (ResidueField A) FSS, Q ∉ N' ∧
              ∃ (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))) (z : ↥(fieldBar q M')), R.IsResidueDisc Q D z ∧ P ∈ D)) := by sorry
