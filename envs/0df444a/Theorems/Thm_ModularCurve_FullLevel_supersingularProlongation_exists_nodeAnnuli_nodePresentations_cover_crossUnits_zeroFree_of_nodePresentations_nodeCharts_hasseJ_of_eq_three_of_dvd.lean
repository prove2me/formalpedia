-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_nodeAnnuli_nodePresentations_cover_crossUnits_zeroFree_of_nodePresentations_nodeCharts_hasseJ_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_exists_nodeAnnuli_nodePresentations_cover_crossUnits_zeroFree_of_nodePresentations_nodeCharts_hasseJ_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/168bc973-b510-5e06-8d75-518577a39ba8
-- title:
--   Node annuli at supersingular reduction for q=3
-- statement:
--   Throughout, $q$ is a prime with $q = 3$, $M'$ is a nonzero level with $q \nmid M'$, and $\ell$ is a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Further, $A$ is a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a non-unit (`A.LiesOverPrime q`, i.e. $q \in A^{\mathrm{nonunits}}$), with residue field $\kappa =$ `ResidueField A`, and $\pi \in A$ satisfies $\pi^{q^2-1} = q$.
--
--   Two function fields inside `LaurentSeries (AlgebraicClosure ℚ)` occur: $F_{M'} =$ `modularFunctionFieldBar M'`, the subfield generated over $\overline{\mathbb Q}$ by the coefficientwise image of the full level-$M'$ modular function field, and $F =$ `fieldBar q M'` $=$ `xHFunctionFieldBar (q^2*M') (levelH q M')`, the corresponding base change of the function field of the modular curve $X_H$ of level $q^2M'$, where $H =$ `levelH q M'` is the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, i.e. the units congruent to $1$ modulo $q$. The hypothesis `hle` is the inclusion $F_{M'} \le F$, and `IntermediateField.inclusion hle` denotes the resulting embedding. For a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`) and $\gamma \in \mathrm{SL}_2(\mathbb Z)$, `levelAutBar q M' ζ γ` is the $\overline{\mathbb Q}$-automorphism of $F$ singled out by the predicate `IsLevelAutBar` (the identity if none exists). Places are understood in the sense of the structure `Place`: a valuation subring containing the base field, not equal to the whole field, whose valuation ring is a principal ideal ring; `ord`, `evalAt` and `IsRational` (surjectivity of the base field onto the residue field) are its order function, its residue evaluation and its rationality.
--
--   The supersingular datum consists of a finset $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$ which by `hW` is exactly `ssPlaces q M' κ` — the rational places satisfying `IsAffineGeomPlace` whose value at `jGeomGen κ M'` lies in `ssJSet q κ` — together with a chosen $s \in W$. Moreover $R_0$ is a `ConstantReduction` of $A$ from $F_{M'}$ to `modularFunctionFieldC κ M'`: a valuation subring `R₀.integers` of $F_{M'}$ meeting $\overline{\mathbb Q}$ in $A$, a surjective residue homomorphism onto `modularFunctionFieldC κ M'` with kernel the maximal ideal, a map on places preserving degrees and compatible with pushforward of divisors. The hypothesis `hR₀` says that every Laurent series $y$ with coefficients in $A$ whose image lies in $F_{M'}$ lies in `R₀.integers` and has residue the coefficientwise reduction of $y$.
--
--   On the side of the special fibre there are: a field $F_{ss}$ over $\kappa$; a `RegularProlongation` $R$ of $A$ from $F$ to $F_{ss}$ (a valuation subring `R.integers` of $F$ meeting $\overline{\mathbb Q}$ in $A$, with surjective residue map onto $F_{ss}$ whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every nonzero element of $F$ has a $\overline{\mathbb Q}$-multiple lying in `R.integers` with nonzero residue); a finset $N$ of places of $F_{ss}$ over $\kappa$ with $|N| = q+1$ (`hcard`); and, indexed by the places $Q$ of $F_{ss}$, subrings $S_Q =$ `Sx Q` of $F$, homomorphisms $\varphi_Q : A[X] \to S_Q$, characters $\chi_{0,Q} : S_Q \to \kappa$ and sets $D_Q =$ `Dx Q` of places of $F$.
--
--   The hypotheses on these are: `h0`, $F_{ss}$ contains an element transcendental over $\kappa$; `h1`, the prolongation $R$ lies over $s$ in the sense that for every $f \in$ `R₀.integers` whose order is non-negative at every place of $F_{M'}$ at which the image $\bar j$ of the $q$-expansion of $j$ has non-negative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $F$ lies in `R.integers` with $R$-residue the image in $F_{ss}$ of $s.\mathrm{evalAt}$ of that $R_0$-residue; `h2`, `R.integers` is preserved by each `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$; `hpkg`, the smooth-point package at each place $Q \notin N$, namely: $A$ maps into $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C\,a)$ is the image of $a$ for $a \in A$; $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$; $\chi_{0,Q}(\varphi_Q X) = 0$; for each $c \in A$ with residue $0$ there is exactly one ring homomorphism $\chi : S_Q \to A$ with $\chi(\varphi_Q(C\,a)) = a$, with residue $\circ\, \chi = \chi_{0,Q}$ and $\chi(\varphi_Q X) = c$; every $f \in S_Q$ lies in `R.integers`, its $R$-residue lies in the valuation subring of $Q$ and reduces there to the image of $\chi_{0,Q}(f)$; the $R$-residue of $\varphi_Q X$ has $Q$-order $1$; $D_Q$ consists exactly of the rational places $P$ at which every $f \in S_Q$ is integral with $P.\mathrm{evalAt}(f) \in A$, and for which $A$-valuation of $P.\mathrm{evalAt}(f)$ is $< 1$ precisely when $\chi_{0,Q}(f) = 0$; each section $\chi$ as above is realised by a unique $P \in D_Q$ with $P.\mathrm{evalAt}(f) = \chi(f)$ throughout $S_Q$; for $P \in D_Q$ the valuation ring of $P$ consists of the fractions $g/h$ with $g,h \in S_Q$ and $P.\mathrm{evalAt}(h) \ne 0$; any nonzero $f$ with $P.\mathrm{ord}\,f = 0$ for all $P \in D_Q$ becomes a unit of $S_Q$ after multiplication by a nonzero constant of $\overline{\mathbb Q}$; and any $f \in$ `R.integers` integral at all $P \in D_Q$ lies in $S_Q$. Next, `hdisj`: the discs $D_Q$, $Q \notin N$, are pairwise disjoint; `hcusp`: for $Q \notin N$ and $P \in D_Q$ the order of $\bar j$ at $P$ is non-negative; `heqv`: for every $\tau$ in the subgroup generated by the automorphisms `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$ which preserves `R.integers`, the induced automorphism `R.resAut τ` of $F_{ss}$ preserves $N$ and carries $D_Q$ to $D_{\mathrm{resAut}\,\tau \cdot Q}$ for $Q \notin N$, where `smulDisc τ D` is $\{P : \tau^{-1}\cdot P \in D\}$; and `hUniq`: for $Q \notin N$, any quadruple $(S,\varphi,\chi_0,D)$ satisfying the same list of clauses has $D = D_Q$, $S = S_Q$ and $\chi_0$ agreeing with $\chi_{0,Q}$.
--
--   The last hypothesis `hC2a` supplies a node block: a finset $N'$ of places of $F_{ss}$ with $|N'| = q+1$; fields $FI_x$ over $\kappa$, regular prolongations $R_x$ of $A$ from $F$ to $FI_x$ and places $b_x$ of $FI_x$, indexed by the places $x$ of $F_{ss}$; an index type $\Lambda$ with subrings $C'_l \subseteq \overline{\mathbb Q}$ contained in $A$, each a discrete valuation domain with element $\varpi'_l$, and a base index $l_0$; complete discrete valuation domains $W_l$ with elements $\pi_{W,l}$, exponents $E_l$ and $E_0$; and, indexed by places $nd$ of $F_{ss}$, sets $S_{nd}$ of places of $F$, subrings $\mathcal N_{nd}$ and local Noetherian subrings $\mathcal N_{0,nd,l}$ of $F$, together with elements $c_{x,nd}, c_{y,nd}, c_{u,nd}$ of $F$; subject to the following clauses. Globally: an element of $C'_l$ has residue $0$ in $A$ exactly when it is divisible by $\varpi'_l$ in $C'_l$; $C'_{l_0} \subseteq C'_l$ for all $l$; $\varpi'_{l_0} \ne 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_{W,l}$ is irreducible and $1 \le E_l$; every $\tau$ in the inertia subgroup of $A$ over $\mathbb Q$ with `A.tameCharacter π τ = 1` fixes $\varpi'_{l_0}$; and $(\varpi'_{l_0})^{E_0} = v\,\pi^{w}$ for some unit $v$ of $A$ and some $w \ge 1$. Per node $nd \in N'$: $b_{nd}$, $nd$ and all places in $S_{nd}$ are rational; $\mathcal N_{nd}$ is the set of $f \in F$ lying in $(R_{nd})$'s and $R$'s integers and integral at every $P \in S_{nd}$; such $f$ have $P.\mathrm{evalAt}(f) \in A$ for $P \in S_{nd}$; $c_{x,nd}c_{y,nd} = (\varpi'_{l_0})^{E_0}c_{u,nd}$; the $R_x$-residue of $c_{x,nd}$ vanishes, the $R$-residue of $c_{x,nd}$ has $nd$-order $1$, the $R$-residue of $c_{y,nd}$ vanishes, and the $R_x$-residue of $c_{y,nd}$ has $b_{nd}$-order $1$ (each stated under the corresponding integrality hypothesis); for $\tau$ in the inertia subgroup with trivial tame character the semilinear automorphism `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ` stabilises $S_{nd}$ and fixes $c_{x,nd}$ and $c_{y,nd}$; every $f \in F$ is a quotient of elements of some $\mathcal N_{0,nd,l}$, and also satisfies $f\,b = \sum_i c_i a_i$ with $a_i, b \in \mathcal N_{0,nd,l_0}$, $b \ne 0$, $c_i \in \overline{\mathbb Q}$; and for each $l$: $\mathcal N_{0,nd,l_0} \subseteq \mathcal N_{0,nd,l} \subseteq \mathcal N_{nd}$; $P \in S_{nd}$ precisely when $\mathcal N_{0,nd,l}$ is contained in the valuation ring of $P$ and every non-unit of it has value at $P$ in the maximal ideal of $A$; $C'_l$ maps into $\mathcal N_{0,nd,l}$; every element of $\mathcal N_{0,nd,l}$ differs from an element of $C'_l$ by a non-unit; any finite family in $\mathcal N_{0,nd,l}$ annihilated by a $C'_l$-linearly independent family of coefficients from $\overline{\mathbb Q}$ is zero; there is a subring $B \subseteq \mathcal N_{0,nd,l}$ containing $c_{x,nd}, c_{y,nd}, c_{u,nd}$, finitely generated over the image of $C'_l$, with $\mathcal N_{0,nd,l}$ the set of fractions $g/h$, $g,h \in B$, $h$ a unit of $\mathcal N_{0,nd,l}$; $c_{x,nd}, c_{y,nd} \in \mathcal N_{0,nd,l}$ and $c_{u,nd}$ is a unit there; and there are a homomorphism $\sigma : W_l \to$ the maximal-adic completion of $\mathcal N_{0,nd,l}$ and a ring isomorphism $\iota$ of that completion with `UVCrossingModel (Wc l) (πW l ^ E l)` $=$ two-variable power series over $W_l$ modulo $X_0X_1 - \pi_{W,l}^{E_l}$, such that $\sigma(\pi_{W,l})$ is the image of $\varpi'_l$ when the latter lies in $\mathcal N_{0,nd,l}$, $\iota \circ \sigma$ is the constant map `const`, every element of $C'_l$ inside $\mathcal N_{0,nd,l}$ is in the image of $\sigma$, and elements $f$ with nonzero $R_x$-residue of $b_{nd}$-order $n$ satisfy $\iota f \equiv \gamma\,V^n$ modulo the ideal generated by `const (πW l)` and $U$ for some unit $\gamma$, while elements with nonzero $R$-residue of $nd$-order $n$ satisfy $\iota f \equiv \gamma\,U^n$ modulo the ideal generated by `const (πW l)` and $V$, where $U$ and $V$ denote the two distinguished elements of the crossing model. Finally `hC2a` requires: the sets $S_{nd}$, $nd \in N'$, are pairwise disjoint; each $P \in S_{nd}$ specialises to $s$, in the sense that for every $f \in$ `R₀.integers` satisfying the two conditions of `h1` and every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference $P.\mathrm{evalAt}(f) - a$ lies in the maximal ideal of $A$; for each $\zeta'$ and $\gamma \in \Gamma_0(M')$ a self-map $\tau_N$ of places preserving $N'$ which transports the sets $S$ and the integers of the $R_x$ along `levelAutBar q M' ζ' γ`; for each $\tau$ in the subgroup generated by the level automorphisms preserving `R.integers`, the invariance of $N'$ and $S_{nd} \mapsto S_{\mathrm{resAut}\,\tau\cdot nd}$; that `R₀.integers` maps into the integers of each $R_{nd}$; for each $nd \in N'$ a ring homomorphism $j$ from `modularFunctionFieldC κ M'` to $FI_{nd}$ compatible with the residues of $R_0$ and $R_{nd}$ and identifying the valuation subring of $s$ with the preimage of that of $b_{nd}$; an Igusa-type clause asserting that `jqNModC (AlgebraicClosure ℚ) q` lies in $F$ and that for some $a_0 \in A$ the difference $\delta$ of the two lies in `R.integers` with vanishing residue, that the $q$-th power of the residue of $a_0$ equals $s.\mathrm{evalAt}(\mathtt{jGeomGen}\ \kappa\ M')$, and that for some $c' \in \overline{\mathbb Q}$ the element $c'\delta$ lies in `R.integers` with nonzero residue and, for each $nd \in N'$, $\delta$ lies in the integers of $R_{nd}$ with nonzero residue and $nd.\mathrm{ord}$ of the $R$-residue of $c'\delta$ equals minus $b_{nd}.\mathrm{ord}$ of the $R_{nd}$-residue of $\delta$; two separation clauses, one producing for $x \in N'$ and $y \notin N'$ an element $g \in$ `R.integers` $\cap\ \mathcal N_{0,x,l_0}$ which is a non-unit there, has nonzero $R$-residue of $y$-order $0$, and is integral at every rational place where $\bar j$ has non-negative order, the other producing for $x \ne x'$ in $N'$ an element $g$ which is $c_{x,x}$ times a unit of $\mathcal N_{0,x,l_0}$ and a unit of $\mathcal N_{0,x',l_0}$; and a dichotomy, that every rational place of $F$ specialising to $s$ lies either in some $S_{nd}$, $nd \in N'$, or in a set $D$ with `R.IsResidueDisc Q D z` for some $Q \notin N'$ and some $z$.
--
--   The conclusion asserts the existence of a family $\mathrm{An}$ of annuli of $F$ over $A$, indexed by the places of $F_{ss}$ over $\kappa$ — each `Annulus A F` packaging a set of places `dom`, a parameter `param` $\in F$ and a modulus in the maximal ideal of $A$, subject to the structure axioms of that notion (rationality and integrality of the parameter on `dom` with value of positive valuation factoring the modulus, the existence and uniqueness of a point of `dom` with prescribed parameter value, $P.\mathrm{ord}(\mathrm{param} - P.\mathrm{evalAt}\,\mathrm{param}) = 1$, and a unit principle) — with the following properties.
--
--   First, for each $x \in N$: the parameter of $\mathrm{An}_x$ lies in `R.integers`, its $R$-residue has $x$-order $1$, and for every $f \in$ `R.integers` with nonzero $R$-residue and $P.\mathrm{ord}\,f = 0$ at all $P \in \mathrm{An}_x.\mathrm{dom}$, and every such $P$, the element $P.\mathrm{evalAt}(f)\cdot(P.\mathrm{evalAt}\,\mathrm{param})^{-x.\mathrm{ord}(R\text{-residue of }f)}$ lies in $A$ and is a unit there; the modulus of $\mathrm{An}_x$ is nonzero in $\overline{\mathbb Q}$; no place of $\mathrm{An}_x.\mathrm{dom}$ lies in any smooth disc $D_Q$ with $Q \notin N$; and every place of $\mathrm{An}_x.\mathrm{dom}$ specialises to $s$ in the sense described above.
--
--   Second, the domains of $\mathrm{An}_x$ and $\mathrm{An}_{x'}$ for $x, x' \in N$ are disjoint unless $x = x'$. Third, for every $\tau$ in the subgroup generated by the automorphisms `levelAutBar q M' ζ γ`, $\gamma \in \Gamma_0(M')$, which preserves `R.integers`, and every $x \in N$, one has `smulDisc τ (An x).dom = (An (R.resAut τ hτ • x)).dom`. Fourth, a covering statement: every rational place $P$ of $F$ which specialises to $s$ lies either in $D_Q$ for some $Q \notin N$ or in $\mathrm{An}_x.\mathrm{dom}$ for some $x \in N$. Fifth, a zero-free test function for each ordered pair $x \ne x'$ in $N$: an element $g \in$ `R.integers` with nonzero $R$-residue whose $x$-order is nonzero, with $P.\mathrm{ord}\,g = 0$ at all $P \in \mathrm{An}_x.\mathrm{dom}$, and which at every $P \in \mathrm{An}_{x'}.\mathrm{dom}$ is integral with $P.\mathrm{evalAt}(g)$ a unit of $A$.
--
--   Sixth, a node block indexed by $N$: there exist data $FI_x, R_x, b_x, \Lambda, C', \varpi', l_0, W_l, \pi_W, E, E_0, S, \mathcal N, \mathcal N_0, c_x, c_y, c_u$ of the same shape as in `hC2a`, satisfying all the global clauses listed there (divisibility description of the residue on each $C'_l$, the chain $C'_{l_0} \subseteq C'_l$, $\varpi'_{l_0} \ne 0$, algebraicity of $A$ over $C'_{l_0}$, irreducibility of $\pi_{W,l}$ and $1 \le E_l$, invariance of $\varpi'_{l_0}$ under tame-trivial inertia, and $(\varpi'_{l_0})^{E_0} = v\pi^w$ with $w \ge 1$), all the per-node clauses listed there for every $nd \in N$ (rationality, the description of $\mathcal N_{nd}$, integrality of values at $S_{nd}$, the cross relation $c_{x,nd}c_{y,nd} = (\varpi'_{l_0})^{E_0}c_{u,nd}$ with the four order and vanishing conditions on $c_{x,nd}$ and $c_{y,nd}$, inertia invariance of $S_{nd}$, $c_{x,nd}$ and $c_{y,nd}$, the two fraction representations of arbitrary elements of $F$, and, for each $l$, the inclusions, the valuative description of $S_{nd}$, the position of $C'_l$, approximation of elements by $C'_l$ modulo non-units, the linear independence clause, the finitely generated subring $B$ with its localisation description, membership and unit status of $c_{x,nd}, c_{y,nd}, c_{u,nd}$, and the pair $(\sigma,\iota)$ identifying the maximal-adic completion of $\mathcal N_{0,nd,l}$ with `UVCrossingModel (Wc l) (πW l ^ E l)` together with the two $U$/$V$ order-$n$ congruences), the Igusa-type clause on `jqNModC (AlgebraicClosure ℚ) q` and $a_0$ stated for all $nd \in N$, the pairwise disjointness of the $S_{nd}$ for $nd \in N$, the specialisation of every $P \in S_{nd}$ to $s$, the existence for each $\zeta'$ and $\gamma \in \Gamma_0(M')$ of a self-map $\tau_N$ preserving $N$ and transporting the $S_{nd}$ and the integers of the $R_{nd}$ along `levelAutBar q M' ζ' γ`, the invariance of $N$ and the transport $S_{nd} \mapsto S_{\mathrm{resAut}\,\tau\cdot nd}$ under the subgroup generated by the level automorphisms preserving `R.integers`, the identification $S_{nd} = \mathrm{An}_{nd}.\mathrm{dom}$ for every $nd \in N$, the fact that `R₀.integers` maps into the integers of each $R_{nd}$, and, for each $nd \in N$, the existence of a ring homomorphism $j$ from `modularFunctionFieldC κ M'` to $FI_{nd}$ compatible with the residues of $R_0$ and $R_{nd}$ and matching the valuation subring of $s$ with that of $b_{nd}$. The two separation clauses and the dichotomy clause of `hC2a` are not part of this block; their counterparts appear as the fifth and fourth conjuncts above.
--
--   This is the node-side step in the construction of the semistable reduction of the modular curve of level $q^2M'$ at a supersingular point of the level-$M'$ fibre, in the case $q = 3$ at an auxiliary level rigidified by a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$: a node block over an unspecified set $N'$ of $q+1$ places is converted into annuli attached to the $q+1$ ends indexed by the given set $N$, together with disjointness from the smooth residue discs, equivariance under the level automorphisms, the covering of all rational places specialising to $s$, separating test functions, and a node block over $N$ whose sets of places are exactly the annulus domains. It feeds [`ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_exists_nodeAnnuli_nodePresentations_cover_crossUnits_zeroFree_of_nodePresentations_nodeCharts_hasseJ_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_exists_nodeAnnuli_nodePresentations_cover_crossUnits_zeroFree_of_nodePresentations_nodeCharts_hasseJ_of_eq_three_of_dvd
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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (N : Finset (Place (ResidueField ↥A) FSS))
    (Sx : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
    (φx : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥A →+* ↥(Sx Q)))
    (χ₀x : (Q : Place (ResidueField ↥A) FSS) → (↥(Sx Q) →+* ResidueField ↥A))
    (Dx : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (h0 : (∃ t : FSS, Transcendental (ResidueField A) t))
    (h1 : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))))
    (h2 : (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers))
    (hcard : N.card = q + 1)
    (hpkg : (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

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
          (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ Dx Q, f ∈ P.toValuationSubring) → f ∈ Sx Q)))
    (hdisj : (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ P, P ∈ Dx Q → P ∈ Dx Q' → Q = Q'))
    (hcusp : (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : fieldBar q M')))
    (heqv : (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
            ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
          ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
            (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
            (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q))))

    (hUniq : (∀ Q ∉ N, ∀ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
          (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          (
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S) ∧
            (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧
            (∀ a : ↥A, ((φ (Polynomial.C a) : ↥(S)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φ Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S)) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S)) →
          (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ D ↔ P ∈ Dx Q) ∧
          (∀ f : ↥(fieldBar q M'), f ∈ S ↔ f ∈ Sx Q) ∧
          (∀ (f : ↥(fieldBar q M')) (hf : f ∈ S) (hf' : f ∈ Sx Q), χ₀ ⟨f, hf⟩ = χ₀x Q ⟨f, hf'⟩)))

    (hC2a :
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

        (∀ nd ∈ N',

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
            ∃ (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))) (z : ↥(fieldBar q M')), R.IsResidueDisc Q D z ∧ P ∈ D))) :
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
                j g ∈ (bx nd).toValuationSubring))) := by sorry
