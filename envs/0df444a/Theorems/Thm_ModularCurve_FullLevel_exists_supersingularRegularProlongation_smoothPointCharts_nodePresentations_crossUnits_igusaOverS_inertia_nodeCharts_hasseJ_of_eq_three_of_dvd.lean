-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/14e9d8c6-871c-59dc-a01b-6c64abe07231
-- title:
--   Supersingular prolongation at q=3: charts, annuli, node models, Drinfeld identification
-- statement:
--   Throughout, $\bar{\mathbb Q}$ denotes `AlgebraicClosure ℚ`; $q$ is a prime with $q=3$; $M'$ is a nonzero natural number with $q \nmid M'$; $\ell$ is a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$; $A$ is a valuation subring of $\bar{\mathbb Q}$ with `A.LiesOverPrime q`, i.e. $q$ lies in the non-units of $A$, and $\kappa := \mathrm{ResidueField}\,A$. Here $F :=$ `fieldBar q M'` is the intermediate field `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')` of $\bar{\mathbb Q}((t))$, where `levelH q M'` is the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, and $F_0 :=$ `modularFunctionFieldBar M'` is the base change to $\bar{\mathbb Q}$ of the full modular function field of level $M'$; $\mathcal F_\kappa :=$ `modularFunctionFieldC κ M'` is the subfield of $\kappa((t))$ generated over $\kappa$ by $j$ and $j(M'\tau)$. A `Place K F` is a valuation subring of $F$ containing the image of $K$, different from $F$ and a principal ideal ring; `ord`, `evalAt` and `IsRational` (surjectivity of $K \to$ residue field) are as in the project's place formalism.
--
--   The hypotheses are: a finite set $W$ of places of $\mathcal F_\kappa$ over $\kappa$ with `hW` saying that $W$ consists exactly of the places satisfying `IsSupersingularPlace q M' κ`; an inclusion `hle` of $F_0$ into $F$; a constant reduction $R_0$ of $A$ from $F_0$ to $\mathcal F_\kappa$ (a valuation subring `R₀.integers` of $F_0$ with a surjective residue map onto $\mathcal F_\kappa$ whose kernel is the maximal ideal, compatible with $A$ on constants, satisfying the scaling property that every nonzero element becomes of nonzero residue after multiplication by a suitable constant, together with a map on places preserving degrees and compatible with divisors); the hypothesis `hR₀` that for every Laurent series $y$ over $A$ whose image in $\bar{\mathbb Q}((t))$ lies in $F_0$, that image lies in `R₀.integers` and its $R_0$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction of $y$; a chosen element $s \in W$; and an element $\pi \in A$ with $\pi^{q^2-1} = q$.
--
--   The conclusion asserts the existence of a type $F_{ss}$ with a field structure and a $\kappa$-algebra structure, and of a regular prolongation $R$ of $A$ from $F$ to $F_{ss}$ (a valuation subring `R.integers` of $F$, a surjective residue map to $F_{ss}$ with kernel the maximal ideal, compatibility with $A$ on constants, and the scaling property), such that all of the following hold.
--
--   (1) $F_{ss}$ contains an element transcendental over $\kappa$.
--
--   (2) Specialisation over $s$: for every $f \in F_0$ lying in `R₀.integers` which is regular at every place of $F_0$ over $\bar{\mathbb Q}$ at which the $q$-expansion of $j$ (the element `coeffEmb (AlgebraicClosure ℚ) jq` of $F_0$) is regular, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $F$ lies in `R.integers` and its $R$-residue is the image in $F_{ss}$ of the value at $s$ of that $R_0$-residue.
--
--   (3) Level invariance: for every $\zeta \in$ `Idx q` (a primitive $q$-th root of unity in $\bar{\mathbb Q}$) and every $\gamma \in \Gamma_0(M')$, the pullback of `R.integers` along `levelAutBar q M' ζ γ` is `R.integers`.
--
--   Furthermore there exist a finite set $N$ of places of $F_{ss}$ over $\kappa$, subrings $S_Q \subseteq F$, ring maps $\varphi_Q : A[X] \to S_Q$ and $\chi_{0,Q} : S_Q \to \kappa$, and sets $D_Q$ of places of $F$ over $\bar{\mathbb Q}$, indexed by the places $Q$ of $F_{ss}$, with the following properties.
--
--   (4) $\#N = q+1$.
--
--   (5) Smooth-point charts: for every $Q \notin N$: the image of $A$ lies in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C a)$ is the image of $a$ in $F$ and $\chi_{0,Q}(\varphi_Q(Ca))$ is the residue of $a$, for $a \in A$; $\chi_{0,Q}(\varphi_Q(X)) = 0$; for every $c \in A$ of residue $0$ there is a unique ring map $\chi : S_Q \to A$ with $\chi \circ \varphi_Q \circ C = \mathrm{id}$, with $\mathrm{res}_A \circ \chi = \chi_{0,Q}$ and with $\chi(\varphi_Q(X)) = c$; every $f \in S_Q$ lies in `R.integers`, its $R$-residue lies in the valuation subring of $Q$, and the residue there is the image of $\chi_{0,Q}(f)$ under $\kappa \to Q.\mathrm{ResidueField}$; $\varphi_Q(X)$ lies in `R.integers` and its $R$-residue has $Q$-order $1$; $D_Q$ consists precisely of the rational places $P$ of $F$ such that every $f \in S_Q$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f) \in A$, and such that $A$-valuation of $P.\mathrm{evalAt}(f)$ is $<1$ if and only if $\chi_{0,Q}(f)=0$; every ring map $\chi : S_Q \to A$ with $\chi \circ \varphi_Q \circ C = \mathrm{id}$ and $\mathrm{res}_A \circ \chi = \chi_{0,Q}$ is realised by a unique $P \in D_Q$ via $P.\mathrm{evalAt}$; for $P \in D_Q$ the valuation subring of $P$ is the set of $f$ with $f h = g$ for some $g,h \in S_Q$ with $P.\mathrm{evalAt}(h) \neq 0$; every nonzero $f \in F$ with $P.\mathrm{ord}(f) = 0$ for all $P \in D_Q$ becomes a unit of $S_Q$ after multiplication by a nonzero constant; and every $f \in$ `R.integers` lying in the valuation subring of every $P \in D_Q$ belongs to $S_Q$.
--
--   (6) Disjointness: if $Q, Q' \notin N$ and $D_Q \cap D_{Q'} \neq \emptyset$ then $Q = Q'$.
--
--   (7) Absence of cusps: for $Q \notin N$ every $P \in D_Q$ satisfies $0 \le P.\mathrm{ord}$ of the image in $F$ of the $q$-expansion of $j$.
--
--   (8) Level equivariance: for every $\tau$ in the subgroup of $\mathrm{Aut}_{\bar{\mathbb Q}}(F)$ generated by the `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$, and every proof that $\tau$ preserves `R.integers`, the induced residual automorphism `R.resAut` permutes $N$ (membership is preserved in both directions), and for $Q \notin N$ one has `smulDisc τ (Dx Q)` $= D_{\,\mathrm{resAut}(\tau)\cdot Q}$, where `smulDisc τ D` $= \{P : \tau^{-1}\cdot P \in D\}$.
--
--   (9) Drinfeld identification: for every $\mathbb F_{q^2}$-algebra structure on $\kappa$, assuming [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, and for every $\zeta \in$ `Idx q`, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity in $\mathbb F_{q^2}$ and a $\kappa$-algebra isomorphism $e$ from $F_{ss}$ onto [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) (the fixed field in the Drinfeld function field of the subgroup generated by the elements $(1,\zeta')$, $\zeta' \in C_s$) such that $\#C_s = 2\,\cdot$ `placeWidthChar q M' s`, and such that for $\gamma \in \Gamma_0(M')$, with $\gamma$ reduced mod $q$ and paired with $1$ in `hSubgroup q`, $e$ intertwines the residual automorphism of `levelAutBar q M' ζ γ⁻¹` with `hFunctionFieldAction` of $(\bar\gamma,1)$.
--
--   (10) Semilinear transport: for every semilinear automorphism $g$ of $F$ over $\bar{\mathbb Q}$ (a pair of ring automorphisms of $F$ and of $\bar{\mathbb Q}$ compatible with the structure map) such that $g$ preserves $A$ on constants, preserves `R.integers`, and fixes the image of the $q$-expansion of $j$, and for every ring automorphism $\psi$ of $\kappa$ compatible with $g$ on residues of elements of $A$, and every ring automorphism $\varphi$ of $F_{ss}$ with $R.\mathrm{residue}(g\cdot f) = \varphi(R.\mathrm{residue}(f))$ for $f \in$ `R.integers`: if $Q \notin N$ and $Q'$ is the transport of $Q$ along $\varphi$ (membership in $Q'$ of $y$ being membership in $Q$ of $\varphi^{-1}(y)$), then $Q' \notin N$, one has $f \in S_Q \iff g\cdot f \in S_{Q'}$, $\chi_{0,Q'}(g \cdot f) = \psi(\chi_{0,Q}(f))$ for $f \in S_Q$, and $P \in D_Q \iff g\cdot P \in D_{Q'}$.
--
--   (11) Transitivity on $N$: any two elements of $N$ are carried one to the other by the residual automorphism of some `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$ preserving `R.integers`.
--
--   (12) For every $Q \notin N$ some such residual level automorphism moves $Q$.
--
--   (13) Generation: there are finitely many elements $g_0,\dots,g_{n-1}$ of `R.integers` such that each $g_i$ lies in the valuation subring of every $P \in D_Q$ for every $Q \notin N$, with $P.\mathrm{evalAt}(g_i) \in A$, and such that every $f \in F_{ss}$ lying in the valuation subring of every $Q \notin N$ belongs to the $\kappa$-subalgebra generated by the $R$-residues of the $g_i$.
--
--   (14) Annuli at the nodes: there is a family of annuli $\mathrm{An}(x)$ over $A$ in $F$ (each given by a set $\mathrm{dom}$ of places, a parameter, and a modulus in the maximal ideal of $A$, subject to the `Annulus` axioms: the places of $\mathrm{dom}$ are rational, the parameter reduces into the maximal ideal of $A$ with nonzero value factoring the modulus, every admissible value of the parameter is attained at exactly one place of $\mathrm{dom}$, the parameter minus its value has order $1$, and a unit principle for functions of order $0$ on the annulus) indexed by the places of $F_{ss}$, such that: for $x \in N$ the parameter lies in `R.integers` with $x$-order of its residue equal to $1$, and for $f \in$ `R.integers` with nonzero residue and order $0$ at all places of $\mathrm{An}(x)$, the product of $P.\mathrm{evalAt}(f)$ with the $(-x.\mathrm{ord}(R.\mathrm{residue}\,f))$-th power of the value of the parameter is a unit of $A$ at each $P \in \mathrm{An}(x).\mathrm{dom}$; the modulus of $\mathrm{An}(x)$ is nonzero; no place of $\mathrm{An}(x).\mathrm{dom}$ lies in any $D_Q$ with $Q \notin N$; every place of $\mathrm{An}(x).\mathrm{dom}$ specialises over $s$, in the sense that for $f$ as in (2) and every $a \in A$ whose residue is the value at $s$ of the $R_0$-residue of $f$, the difference $P.\mathrm{evalAt}$ of the image of $f$ minus $a$ lies in the maximal ideal of $A$. Moreover the annuli attached to distinct elements of $N$ have disjoint domains; the level group permutes them, `smulDisc τ (An x).dom` $= \mathrm{An}(\mathrm{resAut}(\tau)\cdot x).\mathrm{dom}$ for $x \in N$; every rational place $P$ of $F$ satisfying the same specialisation condition over $s$ lies in some $D_Q$ with $Q \notin N$ or in some $\mathrm{An}(x).\mathrm{dom}$ with $x \in N$; and for $x \neq x'$ in $N$ there is $g \in$ `R.integers` with nonzero residue, nonzero $x$-order of that residue, order $0$ at all places of $\mathrm{An}(x)$, and integral with unit value at all places of $\mathrm{An}(x')$.
--
--   (15) Node presentations, asserted inside (14): there exist a family of fields $FI_x$ with $\kappa$-algebra structures, regular prolongations $R_x$ of $A$ from $F$ to $FI_x$ and places $b_x$ of $FI_x$, indexed by the places $x$ of $F_{ss}$; an index type $\Lambda$ with subrings $C'_l \subseteq \bar{\mathbb Q}$ contained in $A$, each a domain and a discrete valuation ring, elements $\varpi'_l \in C'_l$, a distinguished $l_0 \in \Lambda$; complete discrete valuation domains $W_l$ with elements $\pi_{W,l}$, exponents $E(l) \in \mathbb N$ and $E_0 \in \mathbb N$; sets $S_{nd}$ of places of $F$, subrings $\mathcal N_{nd} \subseteq F$ and $\mathcal N_{0,nd,l} \subseteq F$, the latter local and Noetherian, and elements $c_x, c_y, c_u$ of $F$ indexed by the places of $F_{ss}$. These satisfy: the residue of an element $d$ of $C'_l$ in $\kappa$ vanishes exactly when $d \in \varpi'_l C'_l$; $C'_{l_0} \subseteq C'_l$ for all $l$; $\varpi'_{l_0} \neq 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_{W,l}$ is irreducible and $E(l) \ge 1$; every $\tau$ in `A.inertiaSubgroupIn ℚ` with `A.tameCharacter π τ` $= 1$ fixes $\varpi'_{l_0}$; and $(\varpi'_{l_0})^{E_0} = v\,\pi^{w}$ in $A$ for some $w \ge 1$ and some unit $v$ of $A$.
--
--   For each $nd \in N$ the following hold (a list of clauses, summarised here): $b_{nd}$, $nd$ and all places of $S_{nd}$ are rational; $\mathcal N_{nd}$ is exactly the set of elements of $F$ lying in `(Rx nd).integers`, in `R.integers` and in the valuation subring of every $P \in S_{nd}$, and such elements have values in $A$ at the places of $S_{nd}$; the crossing relation $c_x c_y = (\varpi'_{l_0})^{E_0} c_u$ holds; $c_x$ has $R_{nd}$-residue $0$ and its $R$-residue has $nd$-order $1$, while $c_y$ has $R$-residue $0$ and its $R_{nd}$-residue has $b_{nd}$-order $1$; for $\tau$ in the inertia subgroup with trivial tame character, the semilinear automorphism `arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ` stabilises $S_{nd}$ and fixes $c_x$ and $c_y$; every element of $F$ is a quotient of elements of some $\mathcal N_{0,nd,l}$, and also a quotient of a $\bar{\mathbb Q}$-linear combination of elements of $\mathcal N_{0,nd,l_0}$ by an element of $\mathcal N_{0,nd,l_0}$; and for each $l$: $\mathcal N_{0,nd,l_0} \subseteq \mathcal N_{0,nd,l} \subseteq \mathcal N_{nd}$; the places of $S_{nd}$ are characterised as those $P$ with $\mathcal N_{0,nd,l}$ inside the valuation subring of $P$ and with the non-units of $\mathcal N_{0,nd,l}$ evaluating into the maximal ideal of $A$; the constants of $C'_l$ lie in $\mathcal N_{0,nd,l}$ and every element of $\mathcal N_{0,nd,l}$ differs from such a constant by a non-unit; families from $\mathcal N_{0,nd,l}$ with $C'_l$-linearly independent coefficient vectors admit no nontrivial vanishing combination; there is a subring $B_x \subseteq \mathcal N_{0,nd,l}$ containing $c_x, c_y, c_u$, generated by the constants of $C'_l$ together with a finite set, of which $\mathcal N_{0,nd,l}$ is the localisation at the elements becoming units; $c_x, c_y \in \mathcal N_{0,nd,l}$ and $c_u$ is a unit there; and there are a ring map $\sigma$ from $W_l$ to the adic completion of $\mathcal N_{0,nd,l}$ at its maximal ideal and a ring isomorphism $\iota$ of that completion with the crossing model `UVCrossingModel (Wc l) (πW l ^ E l)` (a quotient of the two-variable power series ring over $W_l$) such that $\sigma(\pi_{W,l})$ is the image of $\varpi'_l$, $\iota \circ \sigma$ is the constant map, every constant from $C'_l$ lying in $\mathcal N_{0,nd,l}$ is in the image of $\sigma$, and the leading-term conditions hold: an element whose $R_{nd}$-residue is nonzero of $b_{nd}$-order $n$ has image congruent to $\gamma V^n$ modulo the ideal generated by $\pi_{W,l}$ and $U$ for some unit $\gamma$, and symmetrically an element whose $R$-residue is nonzero of $nd$-order $n$ has image congruent to $\gamma U^n$ modulo the ideal generated by $\pi_{W,l}$ and $V$.
--
--   In addition: (Hasse invariant clause) the Laurent series `jqNModC (AlgebraicClosure ℚ) q` lies in $F$, and there are $a_0 \in A$ such that the difference of that element and $a_0$ lies in `R.integers` with $R$-residue $0$, with $\mathrm{res}_A(a_0)^q$ equal to the value at $s$ of `jGeomGen κ M'`, and a constant $c'$ such that $c'$ times this difference lies in `R.integers` with nonzero residue and, for every $nd \in N$, the difference lies in `(Rx nd).integers` with nonzero residue, the $nd$-order of the $R$-residue of the scaled difference being minus the $b_{nd}$-order of the $R_{nd}$-residue of the difference. The sets $S_{nd}$, $nd \in N$, are pairwise disjoint; every place of $S_{nd}$ satisfies the specialisation condition over $s$ of (2) and (14); for every $\zeta'$ and $\gamma \in \Gamma_0(M')$ there is a map $\tau_N$ of places of $F_{ss}$ preserving $N$ with $(\mathrm{levelAutBar}\,\zeta'\,\gamma)\cdot P \in S_{nd} \iff P \in S_{\tau_N(nd)}$ and with the pullback of `(Rx nd).integers` along that automorphism equal to `(Rx (τN nd)).integers`; for $\tau$ in the subgroup generated by the level automorphisms and preserving `R.integers`, the residual automorphism preserves $N$ and carries $S_{nd}$ to $S_{\mathrm{resAut}(\tau)\cdot nd}$; $S_{nd} = \mathrm{An}(nd).\mathrm{dom}$ for $nd \in N$; the images in $F$ of elements of `R₀.integers` lie in `(Rx nd).integers`; and for each $nd \in N$ there is a ring map $j_{nd} : \mathcal F_\kappa \to FI_{nd}$ compatible with the $R_0$- and $R_{nd}$-residues, under which membership in the valuation subring of $s$ corresponds to membership in the valuation subring of $b_{nd}$.
--
--   (16) Drinfeld identification with inertia: for every ring map $\iota : \mathbb F_{q^2} \to \kappa$, taken as the algebra structure, and assuming [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, there is a subgroup $C_s$ of the $(q+1)$-st roots of unity in $\mathbb F_{q^2}$ with $\#C_s = 2\,\cdot$ `placeWidthChar q M' s` such that for every $\zeta \in$ `Idx q` there are $\eta \in \{1,q\}$ and a $\kappa$-algebra isomorphism $e$ of $F_{ss}$ with [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) satisfying: the $\Gamma_0(M')$-equivariance of (9), $e$ intertwining the residual automorphism of `levelAutBar q M' ζ γ⁻¹` with the action of $(\bar\gamma,1)$; and, for every $\tau$ in `A.inertiaSubgroupIn ℚ` and every unit $\alpha$ of $\mathbb F_{q^2}$ with $\iota(\alpha) =$ `A.tameCharacter π τ`, the semilinear automorphism $g =$ `arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ` preserves `R.integers`, and for every ring automorphism $\varphi$ of $F_{ss}$ compatible with $g$ on $R$-residues, every $d \in (\mathbb Z/q)^\times$ whose image in $\mathbb F_{q^2}$ is $\alpha^{q+1}$, and every proof that $(\mathrm{diag}(1,(d^{\eta})^{-1}), \alpha^{\eta})$ lies in `hSubgroup q`, the isomorphism $e$ intertwines $\varphi$ with `hFunctionFieldAction` of that element.
--
--   This is the $q=3$ instance, at the rigid auxiliary level imposed by the prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the semistable-reduction package at a supersingular point of the modular curve of level $q^2M'$: it produces, over a chosen supersingular place $s$ of level $M'$ in characteristic $q$, the Gauss-type prolongation whose reduction is a quotient of the function field of the Drinfeld curve $xy^q - x^qy = 1$, together with charts at the smooth points, annuli at the $q+1$ nodes, crossing models for the local rings at the nodes, the Hasse-invariant normalisation of $j$, and the equivariance of all this for the level group $\Gamma_0(M')$, for semilinear transport, and for tame inertia. It is cited by the two statements that extract from it the smooth-point charts with cross units and inertia action, and the tube annuli with widths, discs, node rings and the moduli-theoretic Hasse relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_three_of_dvd
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
