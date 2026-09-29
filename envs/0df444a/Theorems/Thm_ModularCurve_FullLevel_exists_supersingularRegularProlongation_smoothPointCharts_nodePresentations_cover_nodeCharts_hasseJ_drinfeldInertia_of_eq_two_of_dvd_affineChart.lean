-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_of_eq_two_of_dvd_affineChart
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_of_eq_two_of_dvd_affineChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/df1187a4-3dfa-5084-aaaa-9150c712740e
-- title:
--   Supersingular prolongation with charts, nodes and Drinfeld inertia, q=2
-- statement:
--   Setting. Let $q$ be a prime with $q=2$ (hypothesis `hq2`), let $M'$ be a nonzero natural number with $q\nmid M'$ (`hqM'`), and let $\ell$ be a prime with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$ (`hℓ`, `hℓ12`, `hℓM'`). Let $A$ be a valuation subring of $\overline{\mathbb Q}=\,$`AlgebraicClosure ℚ` lying over $q$ in the sense that $q$ is a non-unit of $A$ (`hA`), and write $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of `modularFunctionFieldC κ M'` over $\kappa$ — a place being a valuation subring containing the base field, different from the whole field and a principal ideal ring — which consists exactly of the supersingular places `ssPlaces q M' κ` (`hW`); let $s\in W$. Let `hle` assert the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'` of intermediate fields of `LaurentSeries (AlgebraicClosure ℚ)` over $\overline{\mathbb Q}$, where `fieldBar q M'` is `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`. Let $R_0$ be a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'`: a valuation subring `R₀.integers`, a surjective residue homomorphism onto `modularFunctionFieldC κ M'` with kernel the maximal ideal, compatible with $A$ on constants, admitting constant rescaling of every nonzero element into the integers with nonzero residue, together with a map on places preserving degrees and compatible with divisors of functions. The hypothesis `hR₀` requires that coefficientwise reduction is computed by $R_0$: for every Laurent series $y$ over $A$ whose image under `coeffMap A.subtype` lies in `modularFunctionFieldBar M'`, that image lies in `R₀.integers` and its $R_0$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction of $y$. Finally let $\pi_t\in\overline{\mathbb Q}$ satisfy $\pi_t^{\,q^2-1}=q$ (`hπt`) and $\pi_t\in A$ (`hπA`).
--
--   Throughout, call $f\in$ `R₀.integers` *$j$-regular* when $0\le P.\mathrm{ord}(f)$ for every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the image `coeffEmb (AlgebraicClosure ℚ) jq` of the $q$-expansion of $j$ has non-negative order.
--
--   Conclusion. There exist a field $F_{\mathrm{ss}}$, an algebra structure of $\kappa$ on it, and a `RegularProlongation` $R$ of $A$ from `fieldBar q M'` to $F_{\mathrm{ss}}$ (a valuation subring `R.integers` of `fieldBar q M'` with a surjective residue map onto $F_{\mathrm{ss}}$ whose kernel is the maximal ideal, agreeing with $A$ on constants and compatible with the residue map of $A$, and with the rescaling property), such that the following hold.
--
--   (i) Some element of $F_{\mathrm{ss}}$ is transcendental over $\kappa$.
--
--   (ii) $R$ lies over $s$: for every $f\in$ `R₀.integers` that is $j$-regular and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` under `IntermediateField.inclusion hle` lies in `R.integers` and its $R$-residue is the image under $\kappa\to F_{\mathrm{ss}}$ of $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$.
--
--   (iii) For every $\zeta$ in `Idx q` (the primitive $q$-th roots of unity in $\overline{\mathbb Q}$) and every $\gamma\in\Gamma_0(M')\subseteq \mathrm{SL}_2(\mathbb Z)$, the pullback of `R.integers` along `levelAutBar q M' ζ γ` equals `R.integers`.
--
--   (iv) There exist a finite set $N$ of places of $F_{\mathrm{ss}}$ over $\kappa$, and assignments $Q\mapsto S_Q$ (a subring of `fieldBar q M'`), $Q\mapsto\varphi_Q:\mathrm{Polynomial}\,A\to S_Q$, $Q\mapsto\chi_{0,Q}:S_Q\to\kappa$ and $Q\mapsto D_Q$ (a set of places of `fieldBar q M'` over $\overline{\mathbb Q}$) with $\#N=q+1$ and the following properties.
--
--   (iv.a) For every place $Q\notin N$: $S_Q$ contains all constants from $A$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C\,a)$ is the constant $a$ for $a\in A$; $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$; $\chi_{0,Q}(\varphi_Q(X))=0$; for every $c\in A$ with residue $0$ there is exactly one ring homomorphism $\chi:S_Q\to A$ with $\chi(\varphi_Q(C\,a))=a$ for all $a\in A$, with residue $\circ\,\chi=\chi_{0,Q}$, and with $\chi(\varphi_Q(X))=c$; every $f\in S_Q$ lies in `R.integers`, its $R$-residue lies in the valuation subring of $Q$, and the residue there is the image of $\chi_{0,Q}(f)$ in $Q.\mathrm{ResidueField}$; the $R$-residue of $\varphi_Q(X)$ has $Q$-order $1$; $D_Q$ consists exactly of the rational places $P$ (those with $\overline{\mathbb Q}\to P.\mathrm{ResidueField}$ surjective) at which every $f\in S_Q$ is integral with $P.\mathrm{evalAt}(f)\in A$, and for which $A.\mathrm{valuation}(P.\mathrm{evalAt}(f))<1$ holds if and only if $\chi_{0,Q}(f)=0$; every $A$-section $\chi$ of $\varphi_Q$ as above lifting $\chi_{0,Q}$ is realised by exactly one $P\in D_Q$, through $P.\mathrm{evalAt}(f)=\chi(f)$; for $P\in D_Q$, an element $f$ of `fieldBar q M'` is $P$-integral precisely when $f\cdot h=g$ for some $g,h\in S_Q$ with $P.\mathrm{evalAt}(h)\neq 0$; every nonzero $f$ with $P.\mathrm{ord}(f)=0$ for all $P\in D_Q$ becomes, after multiplication by a nonzero constant of $\overline{\mathbb Q}$, a unit of $S_Q$; and every $f\in$ `R.integers` integral at all $P\in D_Q$ lies in $S_Q$.
--
--   (iv.b) The discs are disjoint: if $Q,Q'\notin N$ and some $P$ lies in $D_Q$ and in $D_{Q'}$, then $Q=Q'$.
--
--   (iv.c) For $Q\notin N$ and $P\in D_Q$, the image in `fieldBar q M'` of `coeffEmb (AlgebraicClosure ℚ) jq` has non-negative $P$-order.
--
--   (iv.d) Equivariance: for every $\tau$ in the subgroup of $\overline{\mathbb Q}$-automorphisms of `fieldBar q M'` generated by the `levelAutBar q M' ζ γ` with $\gamma\in\Gamma_0(M')$, and every hypothesis $h_\tau$ that $\tau$ preserves `R.integers`, the induced residue automorphism `R.resAut τ hτ` of $F_{\mathrm{ss}}$ satisfies: $Q$ lies in $N$ if and only if its translate does, and for $Q\notin N$ the translated disc `RegularProlongation.smulDisc τ (Dx Q)` equals $D$ at the translated place.
--
--   (iv.e) Drinfeld identification. For every algebra structure of $\mathbb F_{q^2}=$`GaloisField q 2` on $\kappa$ such that [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, and every $\zeta$ in `Idx q`, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb F_{q^2}$ and a $\kappa$-algebra isomorphism $e$ of $F_{\mathrm{ss}}$ with the fixed field [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) inside the Drinfeld function field, such that $\#C_s=$ `placeWidthChar q M' s` (the quotient of `jWidthChar q` at the value of `jGeomGen κ M'` at $s$ by the $j$-ramification of $s$), and such that for $\gamma\in\Gamma_0(M')$ with `levelAutBar q M' ζ γ⁻¹` preserving `R.integers` and with $(\mathrm{redQ}\,q\,\gamma,1)$ in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), the conjugate by $e$ of the residue automorphism induced by `levelAutBar q M' ζ γ⁻¹` is `hFunctionFieldAction` at that group element.
--
--   (iv.f) Drinfeld identification with tame inertia. For every ring homomorphism $\iota:\mathbb F_{q^2}\to\kappa$, taken as the algebra structure, such that `CoordRing q κ` is a domain, there is a subgroup $C_s$ with $\#C_s=$ `placeWidthChar q M' s` such that for every $\zeta$ in `Idx q` there are $\eta\in\{1,q\}$ and a $\kappa$-algebra isomorphism $e:F_{\mathrm{ss}}\to$ `quotField q κ Cs` with the same $\Gamma_0(M')$-intertwining as in (iv.e), and moreover: for $\tau$ in the inertia subgroup `A.inertiaSubgroupIn ℚ` and a unit $\alpha$ of $\mathbb F_{q^2}$ with $\iota(\alpha)=$ `A.tameCharacter πt τ`, and for $g$ the semilinear automorphism [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54), the subring `R.integers` is $g$-stable, and for every ring automorphism $\varphi$ of $F_{\mathrm{ss}}$ compatible with $g$ through the residue map of $R$, every unit $d$ of $\mathbb Z/q$ with $\mathrm{algebraMap}(d)=\alpha^{q+1}$, and every proof that $(\mathrm{diagOneElem}\,q\,(d^{\eta})^{-1},\alpha^{\eta})$ lies in `hSubgroup q`, the conjugate of $\varphi$ by $e$ is `hFunctionFieldAction` at that element.
--
--   (iv.g) Cover. There is a subring $B$ of `fieldBar q M'` containing all constants from $A$, contained in `R.integers`, contained in $S_Q$ for every $Q\notin N$, and such that every $z\in F_{\mathrm{ss}}$ integral at all places $Q\notin N$ is the $R$-residue of some element of $B$.
--
--   (iv.h) Node data. There exist a finite set $N'$ of places of $F_{\mathrm{ss}}$ over $\kappa$ with $\#N'=q+1$, together with: for each place $x$ a field $\mathrm{FIx}\,x$ over $\kappa$, a regular prolongation $R_x$ of $A$ from `fieldBar q M'` to it and a place $b_x$ of $\mathrm{FIx}\,x$ over $\kappa$; an index type $\Lambda$ with subrings $C'_l\subseteq\overline{\mathbb Q}$ contained in $A$, each a domain and a discrete valuation ring, elements $\varpi'_l\in C'_l$, a base index $l_0$; complete discrete valuation domains $W_l$ with elements $\pi_l$, exponents $E_l\in\mathbb N$ and $E_0\in\mathbb N$; for each place $nd$ a set $S_{nd}$ of places of `fieldBar q M'` over $\overline{\mathbb Q}$, subrings $\mathcal N_{nd}$ and $\mathcal N_{0,nd,l}$ of `fieldBar q M'`, the latter local (`hloc`) and Noetherian (`hnoe`), and elements $c_x(nd),c_y(nd),c_u(nd)$ of `fieldBar q M'`, subject to the following.
--
--   Global clauses: an element $d$ of $C'_l$ has residue $0$ in $A$ exactly when it is divisible by $\varpi'_l$ in $C'_l$; $C'_{l_0}\subseteq C'_l$ for all $l$; $\varpi'_{l_0}\neq0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_l$ is irreducible and $E_l\ge1$; every $\tau$ in `A.inertiaSubgroupIn ℚ` with `A.tameCharacter πt τ = 1` fixes $\varpi'_{l_0}$; and there are $w\ge1$ and a unit $v$ of $A$ with $(\varpi'_{l_0})^{E_0}=v\,\pi_t^{\,w}$ in $A$.
--
--   For every $nd\in N'$: $b_{nd}$, $nd$ and all members of $S_{nd}$ are rational; $\mathcal N_{nd}$ consists exactly of the elements lying in `(Rx nd).integers`, in `R.integers`, and integral at every $P\in S_{nd}$; elements of $\mathcal N_{nd}$ take values in $A$ at every $P\in S_{nd}$; $c_x(nd)\,c_y(nd)=(\varpi'_{l_0})^{E_0}c_u(nd)$ as elements of `fieldBar q M'`; the $R_{nd}$-residue of $c_x(nd)$ is $0$, the $R$-residue of $c_x(nd)$ has $nd$-order $1$, the $R$-residue of $c_y(nd)$ is $0$, and the $R_{nd}$-residue of $c_y(nd)$ has $b_{nd}$-order $1$ (each stated under the corresponding integrality hypothesis); for $\tau$ in the inertia subgroup with trivial tame character, the semilinear automorphism $g=$ `arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ` preserves $S_{nd}$ and fixes $c_x(nd)$ and $c_y(nd)$; every element of `fieldBar q M'` is a quotient $a/b$ with $a,b\in\mathcal N_{0,nd,l}$ for some $l$, and is also a quotient of a finite $\overline{\mathbb Q}$-linear combination of elements of $\mathcal N_{0,nd,l_0}$ by a nonzero element of $\mathcal N_{0,nd,l_0}$; and for every $l$: $\mathcal N_{0,nd,l_0}\subseteq\mathcal N_{0,nd,l}\subseteq\mathcal N_{nd}$; $S_{nd}$ consists exactly of the places at which all of $\mathcal N_{0,nd,l}$ is integral and at which every non-unit of $\mathcal N_{0,nd,l}$ takes a value in the maximal ideal of $A$; constants from $C'_l$ lie in $\mathcal N_{0,nd,l}$; every $g\in\mathcal N_{0,nd,l}$ differs from some constant of $C'_l$ by a non-unit; finitely many elements of $\mathcal N_{0,nd,l}$ with $C'_l$-linearly independent coefficients in $\overline{\mathbb Q}$ summing to zero must all vanish; there is a subring $B_x\subseteq\mathcal N_{0,nd,l}$ containing $c_x(nd),c_y(nd),c_u(nd)$ such that $\mathcal N_{0,nd,l}$ is obtained from $B_x$ by inverting those of its elements that are units of $\mathcal N_{0,nd,l}$, and $B_x$ is generated by the constants from $C'_l$ together with a finite set; $c_x(nd),c_y(nd)\in\mathcal N_{0,nd,l}$ and $c_u(nd)$ is a unit there; and there are a ring homomorphism $\sigma:W_l\to$ the adic completion of $\mathcal N_{0,nd,l}$ at its maximal ideal and an isomorphism of that completion with `UVCrossingModel (Wc l) (π l ^ E l)` sending $\sigma(\pi_l)$ to the image of the constant $\varpi'_l$, sending $\sigma(o)$ to `const (π l ^ E l) o` for $o\in W_l$, hitting all constants of $C'_l$ in the image of $\sigma$, and with the crossing expansions: an $f\in\mathcal N_{0,nd,l}$ whose $R_{nd}$-residue is nonzero of $b_{nd}$-order $n$ satisfies $\iota(f)-\gamma\,V^{n}\in(\pi_l,U)$ for some unit $\gamma$, and an $f$ whose $R$-residue is nonzero of $nd$-order $n$ satisfies $\iota(f)-\gamma\,U^{n}\in(\pi_l,V)$ for some unit $\gamma$.
--
--   Further clauses for $N'$: the sets $S_{nd}$, $nd\in N'$, are pairwise disjoint; each $P\in S_{nd}$ lies over $s$, in the sense that for $j$-regular $f\in$ `R₀.integers` whose $R_0$-residue lies in the valuation subring of $s$ and for $a\in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference $P.\mathrm{evalAt}(f)-a$ lies in the maximal ideal of $A$; for every $\zeta'$ in `Idx q` and $\gamma\in\Gamma_0(M')$ there is a map $\tau_N$ of places preserving $N'$, compatible with the action of `levelAutBar q M' ζ' γ` on the sets $S_{nd}$ and with the pullback of the subrings `(Rx nd).integers`; for every $\tau$ in the subgroup generated by the level automorphisms, preserving `R.integers`, the induced residue automorphism maps $N'$ into itself and `smulDisc τ (S nd)` is the set at the translated place; for $nd\in N'$ the image of `R₀.integers` lies in `(Rx nd).integers`, and there is a ring homomorphism $j$ from `modularFunctionFieldC κ M'` to $\mathrm{FIx}\,nd$ computing $R_{nd}$-residues of images of $R_0$-integral elements, with $g$ integral at $s$ if and only if $j(g)$ is integral at $b_{nd}$.
--
--   Hasse datum on $j$: the element [`ModularCurve.jqNModC (AlgebraicClosure ℚ) q`](def/ModularCurve_JqCoeff.html#L18) lies in `fieldBar q M'` and there is $a_0\in A$ such that the difference of the two lies in `R.integers` with $R$-residue $0$, the residue of $a_0$ satisfies $\overline{a_0}^{\,q}=s.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M')$, and there is $c'\in\overline{\mathbb Q}$ such that $c'$ times that difference lies in `R.integers` with nonzero $R$-residue and, for every $nd\in N'$, the difference lies in `(Rx nd).integers` with nonzero $R_{nd}$-residue and $nd.\mathrm{ord}$ of the $R$-residue of the scaled difference equals minus the $b_{nd}$-order of that $R_{nd}$-residue.
--
--   Separation: for $x\in N'$ and any place $y\notin N'$ there is $g\in$ `R.integers` lying in $\mathcal N_{0,x,l_0}$, a non-unit there, whose $R$-residue is nonzero of $y$-order $0$, and which is integral at every rational place of `fieldBar q M'` at which the image of `coeffEmb (AlgebraicClosure ℚ) jq` has non-negative order. For distinct $x,x'\in N'$ there is $g$ lying in $\mathcal N_{0,x,l_0}$ and in $\mathcal N_{0,x',l_0}$ which equals $c_x(x)$ times a unit of $\mathcal N_{0,x,l_0}$ and is a unit of $\mathcal N_{0,x',l_0}$.
--
--   Affine chart covering: every rational place $P$ of `fieldBar q M'` over $\overline{\mathbb Q}$ lying over $s$ (in the specialisation sense just described, applied to $P$) either belongs to $S_{nd}$ for some $nd\in N'$, or else there are a place $Q\notin N'$ of $F_{\mathrm{ss}}$, a set $D$ of places of `fieldBar q M'` and $z\in$ `fieldBar q M'` with `R.IsResidueDisc Q D z` — that is, $z$ is a disc coordinate for $D$ over $Q$, the reduction is pointwise computed on $D$ and the degree of divisors supported on $D$ matches the $Q$-order of residues — and $P\in D$.
--
--   This is the $q=2$ instance, at an auxiliary level rigidified by a prime $\ell\equiv 11\pmod{12}$ dividing $M'$, of the construction of the semistable reduction data of the full level-$q$ modular curve above a supersingular point of $X_0(M')$: a regular prolongation lying over the chosen supersingular place, smooth-point charts with their residue discs, node presentations in the crossing model $W[[u,v]]/(uv-\pi^E)$, the identification of the reduced function field with a quotient of the Drinfeld (Igusa-type) curve compatible with $\Gamma_0(M')$ and with tame inertia, and a covering of the rational points over $s$ by nodes and residue discs. It is used in the assembly of the semistable covering of the full level-$q$ curve, through [`ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_of_eq_two_of_dvd_affineChart.lean

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

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_cover_nodeCharts_hasseJ_drinfeldInertia_of_eq_two_of_dvd_affineChart
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
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
