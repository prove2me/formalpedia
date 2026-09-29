-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_of_eq_three_of_dvd_affineChart
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_of_eq_three_of_dvd_affineChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/f547462b-b408-5a18-b057-d57cc2c8b52d
-- title:
--   Supersingular prolongation at q=3: charts, nodes, Drinfeld inertia
-- statement:
--   Throughout, $\overline{\mathbb{Q}}$ denotes `AlgebraicClosure ℚ`. Three fields of Laurent series occur: for a field $K$, `modularFunctionFieldC K M'` is the subfield of $K((t))$ generated over $K$ by the two $q$-expansions `jqModC K` and `jqNModC K M'`; `modularFunctionFieldBar M'` is the coefficientwise base change to $\overline{\mathbb{Q}}$ of `modularFunctionFieldFull M'`; and `fieldBar q M'` is `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, the base change to $\overline{\mathbb{Q}}$ of the function field of the curve of level $q^2M'$ with level group `levelH q M'`, the kernel of the unit-group map `ZMod.unitsMap (dvd_sq_mul q M')`.
--
--   **Data and hypotheses.** A prime $q$ with $q = 3$; a nonzero natural number $M'$ with $q \nmid M'$; a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$ (the rigidity hypotheses on the auxiliary level). A valuation subring $A \subseteq \overline{\mathbb{Q}}$ with `A.LiesOverPrime q`, that is, $q$ is a non-unit of $A$; write $\kappa =$ `ResidueField A`. A finite set $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$ together with `hW`, which says that $W$ consists exactly of the members of `ssPlaces q M' κ`, the places $w$ satisfying `IsSupersingularPlace q M' κ w`. An inclusion of intermediate fields `hle : modularFunctionFieldBar M' ≤ fieldBar q M'`. A constant reduction $R_0$ of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'`: this consists of a valuation subring `R₀.integers`, a surjective residue homomorphism onto `modularFunctionFieldC κ M'` with kernel the maximal ideal, a map on places, compatibility of membership and of residues with $A$, the scaling property that every nonzero element can be multiplied by a constant into the integers with nonzero residue, and preservation of degrees and of divisor pushforwards. A compatibility hypothesis `hR₀`: for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}((t))$ lies in `modularFunctionFieldBar M'`, that element lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. A chosen supersingular place $s \in W$. Finally an element $\pi_t \in \overline{\mathbb{Q}}$ with $\pi_t^{\,q^2-1} = q$ and $\pi_t \in A$.
--
--   **Conclusion.** There exist a field $F_{\mathrm{ss}}$ with a $\kappa$-algebra structure and a regular prolongation $R$ of $A$ to `fieldBar q M'` with residue field $F_{\mathrm{ss}}$ (a valuation subring `R.integers`, a surjective residue map to $F_{\mathrm{ss}}$ with kernel its maximal ideal, compatibility of membership and residues with $A$, and the scaling property) such that the following hold.
--
--   (i) Some $t \in F_{\mathrm{ss}}$ is transcendental over $\kappa$.
--
--   (ii) $R$ lies over $s$: for every $f \in$ `R₀.integers` such that $f$ is regular wherever the image of the $q$-expansion `jq` in `modularFunctionFieldBar M'` is regular (for every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$, $0 \le P.\mathrm{ord}$ of that image implies $0 \le P.\mathrm{ord}\,f$) and such that the $R_0$-residue of $f$ lies in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` lies in `R.integers` and its $R$-residue is the image in $F_{\mathrm{ss}}$ of $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$.
--
--   (iii) For every $\zeta \in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in \Gamma_0(M')$, the pullback of `R.integers` along `levelAutBar q M' ζ γ` is `R.integers`. Here `levelAutBar q M' ζ γ` is the automorphism of `fieldBar q M'` over $\overline{\mathbb{Q}}$ selected by the predicate `IsLevelAutBar q M' ζ γ`, which matches $q$-expansion quotients of modular forms with their $\gamma$-translates under embeddings sending $\zeta$ to $e^{2\pi i/q}$, and the identity if no such automorphism exists.
--
--   Moreover there are a finite set $N$ of places of $F_{\mathrm{ss}}$ over $\kappa$, subrings $S_Q \subseteq$ `fieldBar q M'`, ring homomorphisms $\varphi_Q : A[X] \to S_Q$ and $\chi_{0,Q} : S_Q \to \kappa$, and sets $D_Q$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$, indexed by places $Q$ of $F_{\mathrm{ss}}$, with the following properties.
--
--   (a) $\#N = q+1$, and for every $Q \notin N$: the image of every $a \in A$ lies in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C\,a)$ is the image of $a$ for every $a \in A$; $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$; $\chi_{0,Q}(\varphi_Q X) = 0$; for every $c \in A$ with residue $0$ there is exactly one ring homomorphism $\chi : S_Q \to A$ with $\chi \circ \varphi_Q \circ C = \mathrm{id}$, with residue of $\chi$ equal to $\chi_{0,Q}$, and with $\chi(\varphi_Q X) = c$; every $f \in S_Q$ lies in `R.integers`, its $R$-residue lies in the valuation subring of $Q$, and the residue there is the image of $\chi_{0,Q}(f)$ in $Q$'s residue field; $\varphi_Q X$ lies in `R.integers` and its $R$-residue has $Q$-order $1$; the set $D_Q$ consists exactly of the places $P$ that are rational (the structure map to $P$'s residue field is surjective), on which every $f \in S_Q$ is integral with $P.\mathrm{evalAt}\,f \in A$, and for which $A$-valuation of $P.\mathrm{evalAt}\,f$ is $<1$ precisely when $\chi_{0,Q}(f) = 0$; each $A$-section $\chi$ of $S_Q$ lifting $\chi_{0,Q}$ (that is, $\chi \circ \varphi_Q \circ C = \mathrm{id}$ and residue of $\chi$ equal to $\chi_{0,Q}$) corresponds to exactly one $P \in D_Q$ with $P.\mathrm{evalAt}\,f = \chi f$ for all $f \in S_Q$; for $P \in D_Q$, an element of `fieldBar q M'` is integral at $P$ precisely when it is a quotient $g/h$ with $g,h \in S_Q$ and $P.\mathrm{evalAt}\,h \ne 0$; any nonzero $f$ with $P.\mathrm{ord}\,f = 0$ for all $P \in D_Q$ becomes a unit of $S_Q$ after multiplication by a nonzero constant; and any $f \in$ `R.integers` integral at all $P \in D_Q$ lies in $S_Q$.
--
--   (b) The discs are separated: if $Q, Q' \notin N$ and some $P$ lies in both $D_Q$ and $D_{Q'}$, then $Q = Q'$.
--
--   (c) For $Q \notin N$ and $P \in D_Q$, the image of `jq` in `fieldBar q M'` has $P$-order $\ge 0$.
--
--   (d) Equivariance: for every $\tau$ in the subgroup generated by the automorphisms `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$ that preserves `R.integers`, and every place $Q$, the induced residue automorphism `R.resAut τ` carries $N$ to $N$ (membership is equivalent) and, for $Q \notin N$, carries $D_Q$ to $D_{R.\mathrm{resAut}\,\tau \cdot Q}$ in the sense of `smulDisc`.
--
--   (e) Drinfeld identification. For every $\mathbb{F}_{q^2}$-algebra structure on $\kappa$ for which [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain and every $\zeta \in$ `Idx q`, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and a $\kappa$-isomorphism $e$ of $F_{\mathrm{ss}}$ with the fixed field [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) inside the Drinfeld function field, such that $\#C_s = 2\,$`placeWidthChar q M' s` and $e$ intertwines the residue automorphism of `levelAutBar q M' ζ γ⁻¹` (whenever that automorphism preserves `R.integers`) with the action of $(\overline{\gamma}, 1)$ through `hFunctionFieldAction`, for all $\gamma \in \Gamma_0(M')$ whose reduction $\overline{\gamma} =$ `redQ q γ` gives a member of `hSubgroup q` (the pairs $(g,\alpha)$ with $\det(g)\,\alpha^{q+1} = 1$).
--
--   (f) Drinfeld identification with tame inertia. For every ring homomorphism $\iota : \mathbb{F}_{q^2} \to \kappa$, taken as the algebra structure, and assuming [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, there is a subgroup $C_s$ with $\#C_s = 2\,$`placeWidthChar q M' s` such that for every $\zeta \in$ `Idx q` there are an exponent $\eta \in \{1, q\}$ and a $\kappa$-isomorphism $e$ of $F_{\mathrm{ss}}$ with [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) satisfying the $\Gamma_0(M')$-equivariance of (e) and, in addition, the following. For every $\tau$ in `A.inertiaSubgroupIn ℚ` and every $\alpha \in \mathbb{F}_{q^2}^{\times}$ with $\iota(\alpha) =$ `A.tameCharacter πt τ` (the residue of $\tau\pi_t/\pi_t$), and for the semilinear automorphism $g$ of `fieldBar q M'` given by [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54), the subring `R.integers` is $g$-stable, and for every ring automorphism $\varphi$ of $F_{\mathrm{ss}}$ induced by $g$ on residues, every $d \in (\mathbb{Z}/q)^{\times}$ whose image in $\mathbb{F}_{q^2}$ is $\alpha^{q+1}$, and every witness that $(\,$`diagOneElem q (d ^ η)⁻¹`$, \alpha^{\eta})$ lies in `hSubgroup q`, the map $e$ intertwines $\varphi$ with the action of that pair through `hFunctionFieldAction`.
--
--   (g) Affine chart: there is a subring $B$ of `fieldBar q M'` containing the image of $A$, contained in `R.integers`, contained in $S_Q$ for every $Q \notin N$, and such that every $z \in F_{\mathrm{ss}}$ integral at all $Q \notin N$ is the $R$-residue of some element of $B \cap$ `R.integers`.
--
--   (h) Node data. There are a finite set $N'$ of places of $F_{\mathrm{ss}}$ over $\kappa$ with $\#N' = q+1$; fields $FI_x$ over $\kappa$, regular prolongations $R_x$ of $A$ to `fieldBar q M'` with residue field $FI_x$, and places $b_x$ of $FI_x$ over $\kappa$, indexed by places $x$ of $F_{\mathrm{ss}}$; an index type $\Lambda$ with subrings $C'_l \subseteq \overline{\mathbb{Q}}$ contained in $A$, each a domain and a discrete valuation ring with chosen element $\varpi'_l$, a base index $l_0$; complete discrete valuation rings $W_l$ (commutative domains, adically complete at the maximal ideal) with elements $\pi_l$, exponents $E : \Lambda \to \mathbb{N}$ and $E_0 \in \mathbb{N}$; sets $S_{nd}$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$, subrings $\mathcal{N}_{nd}$ and $\mathcal{N}_{0,nd,l}$ of `fieldBar q M'` with each $\mathcal{N}_{0,nd,l}$ local and Noetherian, and elements $c_x(nd), c_y(nd), c_u(nd)$ of `fieldBar q M'`, indexed by places $nd$ of $F_{\mathrm{ss}}$; subject to: for each $l$, an element of $C'_l$ has residue $0$ in $\kappa$ precisely when it is divisible by $\varpi'_l$ in $C'_l$; $C'_{l_0} \subseteq C'_l$ for all $l$; $\varpi'_{l_0} \ne 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_l$ is irreducible and $E_l \ge 1$; every $\tau$ in `A.inertiaSubgroupIn ℚ` with `A.tameCharacter πt τ` $= 1$ fixes $\varpi'_{l_0}$; and $(\varpi'_{l_0})^{E_0} = v\,\pi_t^{\,w}$ in $A$ for some $w \ge 1$ and some unit $v$ of $A$.
--
--   For each $nd \in N'$: $b_{nd}$, $nd$ and all $P \in S_{nd}$ are rational; $\mathcal{N}_{nd}$ consists exactly of the elements lying in `(Rx nd).integers`, in `R.integers` and integral at every $P \in S_{nd}$, and all such elements have $P.\mathrm{evalAt}$ in $A$ for $P \in S_{nd}$; the crossing relation $c_x(nd)\,c_y(nd) = (\varpi'_{l_0})^{E_0}\,c_u(nd)$ holds; $c_x(nd)$ has $R_{nd}$-residue $0$ and its $R$-residue has $nd$-order $1$, while $c_y(nd)$ has $R$-residue $0$ and its $R_{nd}$-residue has $b_{nd}$-order $1$ (each asserted under the relevant integrality witness); for every $\tau$ in `A.inertiaSubgroupIn ℚ` with trivial tame character at $\pi_t$, the coefficientwise semilinear automorphism $g$ attached to $\tau$ stabilises $S_{nd}$ and fixes $c_x(nd)$ and $c_y(nd)$; every element of `fieldBar q M'` is a quotient $a/b$ with $a, b \in \mathcal{N}_{0,nd,l}$ for some $l$, and also a quotient of a finite $\overline{\mathbb{Q}}$-linear combination of elements of $\mathcal{N}_{0,nd,l_0}$ by a nonzero element of $\mathcal{N}_{0,nd,l_0}$; and for each $l$: $\mathcal{N}_{0,nd,l_0} \subseteq \mathcal{N}_{0,nd,l} \subseteq \mathcal{N}_{nd}$; a place $P$ lies in $S_{nd}$ precisely when $\mathcal{N}_{0,nd,l}$ is integral at $P$ and every non-unit of $\mathcal{N}_{0,nd,l}$ has $P.\mathrm{evalAt}$ in the maximal ideal of $A$; the image of $C'_l$ lies in $\mathcal{N}_{0,nd,l}$ and every element of $\mathcal{N}_{0,nd,l}$ differs from such a constant by a non-unit; elements of $\mathcal{N}_{0,nd,l}$ are linearly independent against $C'_l$-independent scalars (a vanishing combination with $C'_l$-linearly independent coefficients has all its $\mathcal{N}_{0,nd,l}$-entries zero); there is a subring $B_x \subseteq \mathcal{N}_{0,nd,l}$ containing $c_x(nd), c_y(nd), c_u(nd)$ such that $\mathcal{N}_{0,nd,l}$ is the localisation of $B_x$ at the elements of $B_x$ that are units in $\mathcal{N}_{0,nd,l}$, and $B_x$ is generated by the image of $C'_l$ together with a finite set; $c_x(nd), c_y(nd) \in \mathcal{N}_{0,nd,l}$ and $c_u(nd)$ is a unit there; and there are a ring homomorphism $\sigma$ from $W_l$ to the adic completion of $\mathcal{N}_{0,nd,l}$ at its maximal ideal and a ring isomorphism of that completion with the crossing model `UVCrossingModel (Wc l) (π l ^ E l)` (the quotient of `MvPowerSeries (Fin 2) (Wc l)` by `uvCrossingIdeal`), such that $\sigma(\pi_l)$ is the image of $\varpi'_l$, $\sigma$ followed by the isomorphism sends $o$ to `const (π l ^ E l) o`, every constant from $C'_l$ lies in the image of $\sigma$, and the two leading-term statements hold: an element $f$ of $\mathcal{N}_{0,nd,l}$ whose $R_{nd}$-residue is nonzero of $b_{nd}$-order $n$ has image equal to $\gamma\,V^{n}$ modulo the ideal generated by `const (π l ^ E l) (π l)` and $U$, for some unit $\gamma$, and symmetrically an element whose $R$-residue is nonzero of $nd$-order $n$ has image equal to $\gamma\,U^{n}$ modulo the ideal generated by that constant and $V$.
--
--   Finally: distinct members of $N'$ have disjoint sets $S_{nd}$; for $nd \in N'$ and $P \in S_{nd}$, the specialisation of $P$ agrees with $s$, in the sense that for $f \in$ `R₀.integers` regular wherever `jq` is regular and with $R_0$-residue integral at $s$, and for every $a \in A$ whose residue is $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference $P.\mathrm{evalAt}(f) - a$ lies in the maximal ideal of $A$; for each $\zeta'$ and $\gamma \in \Gamma_0(M')$ there is a map $\tau_N$ on places preserving $N'$ with $(\,$`levelAutBar q M' ζ' γ`$) \cdot P \in S_{nd}$ precisely when $P \in S_{\tau_N(nd)}$ and with the pullback of `(Rx nd).integers` along that automorphism equal to `(Rx (τN nd)).integers`; for every $\tau$ in the subgroup generated by the level automorphisms which preserves `R.integers` and every $nd \in N'$, the residue automorphism `R.resAut τ` keeps $nd$ in $N'$ and carries $S_{nd}$ to $S_{R.\mathrm{resAut}\,\tau \cdot nd}$; for $nd \in N'$, the image of `R₀.integers` lies in `(Rx nd).integers`, and there is a ring homomorphism $j$ from `modularFunctionFieldC κ M'` to $FI_{nd}$ compatible with the residues of $R_0$ and $R_{nd}$ and such that an element is integral at $s$ precisely when its $j$-image is integral at $b_{nd}$.
--
--   There is also a Hasse datum on $j$: the element `jqNModC ℚ̄ q` lies in `fieldBar q M'` and there is $a_0 \in A$ such that the difference of these two lies in `R.integers` with $R$-residue $0$, the residue of $a_0$ satisfies $\overline{a_0}^{\,q} = s.\mathrm{evalAt}$ of `jGeomGen κ M'`, and for some $c' \in \overline{\mathbb{Q}}$ the element $c'\,(\,$`jqNModC` $- a_0)$ lies in `R.integers` with nonzero residue while for every $nd \in N'$ the difference lies in `(Rx nd).integers` with nonzero residue and $nd.\mathrm{ord}$ of the $R$-residue equals minus $b_{nd}.\mathrm{ord}$ of the $R_{nd}$-residue.
--
--   Two separation statements: for $x \in N'$ and $y \notin N'$ there is $g \in$ `R.integers` lying in $\mathcal{N}_{0,x,l_0}$ as a non-unit, with nonzero $R$-residue of $y$-order $0$, and integral at every rational place at which `jq` has non-negative order; and for distinct $x, x' \in N'$ there is $g$ lying in both $\mathcal{N}_{0,x,l_0}$ and $\mathcal{N}_{0,x',l_0}$ which equals $c_x(x)$ times a unit in the former and is a unit in the latter.
--
--   Lastly, a covering dichotomy: every rational place $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ whose specialisation agrees with $s$ in the above sense either lies in $S_{nd}$ for some $nd \in N'$, or lies in a residue disc: there are $Q \notin N'$, a set $D$ of places and an element $z$ with `R.IsResidueDisc Q D z` — so $z$ is a disc coordinate at $Q$ for $D$ (all members of $D$ rational with $z$ integral of valuation $<1$, $z \in$ `R.integers` with $Q$-order $1$ of its residue, every $c$ of valuation $<1$ realised by exactly one $P \in D$, $P.\mathrm{ord}(z - P.\mathrm{evalAt}\,z) = 1$, and the unit principle), $D$ is pointwise compatible with $Q$ and the degree condition relating divisors on $D$ with $Q$-orders holds — and $P \in D$.
--
--   This is the construction, in the case $q = 3$ over an auxiliary level divisible by a prime $\ell \equiv 11 \pmod{12}$, of the semistable datum at a supersingular point $s$ of the level-$M'$ curve for the full level-$q$ cover: a single regular prolongation of the valuation ring $A$ together with smooth-point charts, node presentations in crossing form, an affine chart, and the identification of the reduced function field with a Drinfeld quotient field compatible with $\Gamma_0(M')$ and with tame inertia. It is the input to [`ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_three_of_dvd), where the Igusa-type description of the supersingular part of the special fibre is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_of_eq_three_of_dvd_affineChart.lean

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

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_of_eq_three_of_dvd_affineChart
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
            ∀ (ζ : Idx q), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ ∃ (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
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
                    ∀ (hmem : (diagOneElem q (d ^ η)⁻¹, α ^ η) ∈ DrinfeldCurve.hSubgroup q),
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
