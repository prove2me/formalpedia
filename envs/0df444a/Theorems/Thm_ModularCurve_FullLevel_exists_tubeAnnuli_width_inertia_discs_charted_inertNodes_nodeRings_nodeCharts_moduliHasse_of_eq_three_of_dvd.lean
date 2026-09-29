-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_tubeAnnuli_width_inertia_discs_charted_inertNodes_nodeRings_nodeCharts_moduliHasse_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_tubeAnnuli_width_inertia_discs_charted_inertNodes_nodeRings_nodeCharts_moduliHasse_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/4789d862-6a76-5d47-87e5-c1956e92be8e
-- title:
--   Tube annuli and residue discs at a supersingular place (q=3)
-- statement:
--   Throughout, $q$ is a prime with $q=3$, $M'$ is a non-zero natural number not divisible by $q$, and $\ell$ is a prime with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$ (hypotheses `hq3`, `hqM'`, `hℓ`, `hℓ12`, `hℓM'`). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}=\mathrm{AlgebraicClosure}\,\mathbb{Q}$ with `hA : A.LiesOverPrime q`, i.e. $q$ is a non-unit of $A$. The curve in play is `fieldBar q M'`, the $\overline{\mathbb{Q}}$-base change of the function field of the modular curve of level $q^2M'$ attached to the subgroup `levelH q M'` of $(\mathbb{Z}/q^2M')^\times$ (a kernel of a reduction map of unit groups); places are [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22)s, i.e. proper valuation subrings containing the constants and with principal ideals, with their order function `ord` and their evaluation `evalAt` (defined through the inverse of the constants in the residue field), and `IsRational` means that the constants surject onto the residue field of the place.
--
--   Data on the special fibre. $W$ is a finite set of places of `modularFunctionFieldC (ResidueField A) M'` over $\mathrm{ResidueField}\,A$ consisting, by `hW`, exactly of the supersingular places, i.e. of the rational affine geometric places whose value at the generator `jGeomGen` lies in the supersingular $j$-set; `hle` records the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'`. $R_0$ is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField A) M'` (a valuation subring `R₀.integers` lying over $A$, a surjective residue map onto the characteristic-$p$ modular function field with kernel the maximal ideal, compatible with the residue map of $A$, with scaling to non-zero residue, together with a place map preserving degrees and orders), and `hR₀` requires this reduction to agree with coefficientwise reduction of Laurent series with coefficients in $A$. Finally $\zeta$ is a primitive $q$-th root of unity (an element of `Idx q`), and $\pi_t$ is an element of $A$ with $\pi_t^{q^2-1}=q$ (`hπt`, `hπA`).
--
--   Valuation subrings. $O^{\mathrm{Ig}}$ assigns a valuation subring of `fieldBar q M'` to every point of the projective line $\mathbb{P}^1(\mathbb{Z}/q)$ ([`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21); the Lean binder for such a point is again written $\ell$, shadowing the auxiliary prime, and is written $\lambda$ below), and $O^{\mathrm{SS}}$ assigns one to every element of $W$. By `hIg_inf`, $O^{\mathrm{Ig}}(\infty)$ at the point `lineInfty q` consists of those $f$ whose Laurent series can be written as a quotient $x/y$ of coefficient images of Laurent series over $A$ with $y$ of non-zero reduction; by `hIg`, for every point $\lambda$ there is $\gamma\in\Gamma_0(M')$ with $\mathrm{red}_q(\gamma)\cdot\infty=\lambda$ and $O^{\mathrm{Ig}}(\lambda)$ the pullback of $O^{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ`. The hypothesis `hSS` demands, for every $s'\in W$, four properties of $O^{\mathrm{SS}}(s')$: it lies over $A$ (a constant lies in it iff it lies in $A$); there is $t$ in it such that $t-a$ is a unit of it for every $a\in A$; for every $f\in R_0.\mathrm{integers}$ which is integral wherever the base-changed $j$-expansion `coeffEmb jq` is (that is, $0\le P.\mathrm{ord}(j)$ implies $0\le P.\mathrm{ord}(f)$ for all places $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$) and whose $R_0$-residue lies in the valuation subring of $s'$, the image of $f$ in `fieldBar q M'` lies in $O^{\mathrm{SS}}(s')$ and, for every $a\in A$ whose residue equals the value of $s'$ at that $R_0$-residue, $f-a$ lies in the maximal ideal; and $O^{\mathrm{SS}}(s')$ is invariant under the pullback along `levelAutBar q M' ζ' γ` for every $\zeta'$ and every $\gamma\in\Gamma_0(M')$.
--
--   Charts. For each point $\lambda$ a field $F^{\mathrm{Ig}}_\lambda$ over $\mathrm{ResidueField}\,A$ and a `ComponentChart` $C^{\mathrm{Ig}}_\lambda$ of $A$ on `fieldBar q M'` with values in it are given, with `hCIg` identifying its ring of integers with $O^{\mathrm{Ig}}(\lambda)$; for each $s'\in W$ a field $F^{\mathrm{SS}}_{s'}$, a `RegularProlongation` $R^{\mathrm{SS}}_{s'}$ and a `ComponentChart` $C^{\mathrm{SS}}_{s'}$, both with ring of integers $O^{\mathrm{SS}}(s')$ (`hRSS`, `hCSS`). A component chart consists of such a prolongation together with a set `dom` of places of the curve, a finite set `nodes` of places of the residue curve and a place map, subject to the axioms that places of `dom` do not map into `nodes`, a pointwise compatibility of evaluation with residues, and the order/divisor compatibility away from the nodes. Finally $x_s$ assigns to every point $\lambda$ and every $s'\in W$ a place $x_s(\lambda,s')$ of $F^{\mathrm{Ig}}_\lambda$, which is a node of $C^{\mathrm{Ig}}_\lambda$ (`hxs_mem`), and `hxs_over` provides, for each $\lambda$, a ring homomorphism $j_\lambda$ from `modularFunctionFieldC (ResidueField A) M'` to $F^{\mathrm{Ig}}_\lambda$ which computes the $C^{\mathrm{Ig}}_\lambda$-residue of elements of $R_0.\mathrm{integers}$ from their $R_0$-residue, and which pulls the valuation subring of $x_s(\lambda,s')$ back to that of $s'$, for every $s'\in W$.
--
--   One element $s\in W$ is fixed. The assertion is the existence of two families of annuli $\mathrm{An},\mathrm{An}'\colon\mathbb{P}^1(\mathbb{Z}/q)\to\mathrm{Annulus}\,A\,(\mathtt{fieldBar }q\,M')$ and of a family $x_t$ of places of $F^{\mathrm{SS}}_s$ over $\mathrm{ResidueField}\,A$ indexed by $\mathbb{P}^1(\mathbb{Z}/q)$, with the following properties. (An `Annulus` over $A$ consists of a set `dom` of places, a parameter `param` and a modulus in the maximal ideal of $A$, such that the places of `dom` are rational, the parameter is integral there with value a non-zero element of the maximal ideal dividing the modulus, every admissible value of the parameter is attained at a unique place of `dom`, $P.\mathrm{ord}(\mathrm{param}-P.\mathrm{evalAt}\,\mathrm{param})=1$ on `dom`, and a unit principle holds for functions of order $0$ on `dom`.)
--
--   First, the range of $x_t$ is stable under semilinear symmetries: for every semilinear automorphism $g$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ (an element of `SemilinearAut`, i.e. a pair of a ring automorphism of the field and one of $\overline{\mathbb{Q}}$, compatible with the structure map) whose base automorphism preserves $A$ and induces the identity on the residue field of $A$, and which fixes the image of the base-changed $j$-expansion in `fieldBar q M'`, and for every proof that $g$ preserves $R^{\mathrm{SS}}_s.\mathrm{integers}$ and every $\mathrm{ResidueField}\,A$-automorphism $\varphi$ of $F^{\mathrm{SS}}_s$ inducing $g$ on residues, one has $\varphi\cdot Q\in\mathrm{range}\,x_t\iff Q\in\mathrm{range}\,x_t$ for every place $Q$ of $F^{\mathrm{SS}}_s$.
--
--   Secondly, for every point $\lambda$: the two annuli $\mathrm{An}(\lambda)$ and $\mathrm{An}'(\lambda)$ have the same domain and the same modulus; this modulus is non-zero in $\overline{\mathbb{Q}}$ and equals $u\pi_t^{w}$ for some unit $u$ of $A$ and some integer $w\ge 1$; for every $\tau$ in `A.inertiaSubgroupIn ℚ` with `A.tameCharacter πt τ = 1`, the semilinear automorphism $g$ obtained from $\tau$ by [`ModularCurve.arithmeticGalois (xHFunctionField (q^2*M') (levelH q M'))`](def/ModularCurve_ArithmeticGalois.html#L54) (coefficientwise action on Laurent series) stabilises $\mathrm{An}(\lambda).\mathrm{dom}$ and fixes both parameters $\mathrm{An}(\lambda).\mathrm{param}$ and $\mathrm{An}'(\lambda).\mathrm{param}$; and the two parameters are reciprocal up to the modulus: $\mathrm{An}'(\lambda).\mathrm{param}\cdot\mathrm{An}(\lambda).\mathrm{param}$ equals the image of the modulus in `fieldBar q M'`.
--
--   Thirdly, the two ends: for every $\lambda$, $\mathrm{An}(\lambda)$ is attached to $C^{\mathrm{Ig}}_\lambda$ at the node $x_s(\lambda,s)$ in the sense of `Annulus.IsAttached` (the node condition, the parameter integral with residue of order $1$ at the node, and the unit law $P.\mathrm{evalAt}(f)\cdot (P.\mathrm{evalAt}\,\mathrm{param})^{-\mathrm{ord}}$ a unit of $A$ for all functions of non-zero residue and order $0$ on the domain); and, chart-free against $R^{\mathrm{SS}}_s$, the parameter of $\mathrm{An}'(\lambda)$ lies in $R^{\mathrm{SS}}_s.\mathrm{integers}$ with residue of order $1$ at $x_t(\lambda)$, and for every $f\in R^{\mathrm{SS}}_s.\mathrm{integers}$ with non-zero residue and with $P.\mathrm{ord}(f)=0$ for all $P\in \mathrm{An}'(\lambda).\mathrm{dom}$, the product $P.\mathrm{evalAt}(f)\cdot(P.\mathrm{evalAt}\,\mathrm{An}'(\lambda).\mathrm{param})^{-\mathrm{ord}_{x_t(\lambda)}(\text{residue of }f)}$ lies in $A$ and is a unit there, for every such $P$.
--
--   Fourthly, $x_t$ is injective. Fifthly, the domains of the $\mathrm{An}(\lambda)$ are pairwise disjoint: if $P$ lies in $\mathrm{An}(\lambda).\mathrm{dom}$ and in $\mathrm{An}(\lambda').\mathrm{dom}$ then $\lambda=\lambda'$.
--
--   Sixthly, the domains lie in the supersingular tube of $s$: for every $\lambda$, every $P\in\mathrm{An}(\lambda).\mathrm{dom}$, every $f\in R_0.\mathrm{integers}$ integral wherever the base-changed $j$-expansion is and with $R_0$-residue in the valuation subring of $s$, and every $a\in A$ whose residue is the value of $s$ at that residue, the difference $P.\mathrm{evalAt}(f)-a$ lies in $A$ and in its maximal ideal.
--
--   Seventhly, equivariance under the level automorphisms: for every $\zeta'$, every $\gamma\in\Gamma_0(M')$ and every permutation $\sigma$ of $\mathbb{P}^1(\mathbb{Z}/q)$ such that the pullback of $O^{\mathrm{Ig}}(\lambda)$ along `levelAutBar q M' ζ' γ` is $O^{\mathrm{Ig}}(\sigma\lambda)$ for all $\lambda$, the pullback annulus $\mathrm{An}(\lambda).\mathrm{comap}$ along that automorphism has domain $\mathrm{An}(\sigma\lambda).\mathrm{dom}$, and $\mathrm{An}(\lambda)$ and $\mathrm{An}(\sigma\lambda)$ have the same modulus.
--
--   Eighthly, a node-ring package. There exist an index type $\Lambda$ with a distinguished index $l_0$; subrings $C'_l\subseteq\overline{\mathbb{Q}}$ all contained in $A$, each a domain and a discrete valuation ring, with elements $\varpi'_l$; coefficient rings $W_l$ which are complete discrete valuation rings (domains, adically complete at their maximal ideals) with elements $\pi_l$; exponents $E(l)$ and $E_0$ in $\mathbb{N}$; subrings $\mathcal{N}_\lambda$ and $\mathcal{N}_{0,\lambda,l}$ of `fieldBar q M'`, the latter local and Noetherian; and functions $x,y,u$ from $\mathbb{P}^1(\mathbb{Z}/q)$ to `fieldBar q M'`, such that: an element $d$ of $C'_l$ has residue $0$ in $\mathrm{ResidueField}\,A$ exactly when it is divisible by $\varpi'_l$ in $C'_l$; $C'_{l_0}\subseteq C'_l$ for all $l$; $\varpi'_{l_0}\neq 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_l$ is irreducible and $E(l)\ge 1$; and for every point $\lambda$:
--
--   — $\mathrm{An}(\lambda).\mathrm{param}=y(\lambda)$ and $\mathrm{An}(\lambda).\mathrm{modulus}=(\varpi'_{l_0})^{E_0}$ in $\overline{\mathbb{Q}}$;
--   — $x_s(\lambda,s)$ and $x_t(\lambda)$ are rational, and so is every $P\in\mathrm{An}(\lambda).\mathrm{dom}$;
--   — $\mathcal{N}_\lambda$ is exactly the set of $f$ lying in $C^{\mathrm{Ig}}_\lambda.\mathrm{integers}$, in $R^{\mathrm{SS}}_s.\mathrm{integers}$ and in the valuation subring of every $P\in\mathrm{An}(\lambda).\mathrm{dom}$, and every such $f$ has $P.\mathrm{evalAt}(f)\in A$ for every $P$ in that domain;
--   — the crossing relation $x(\lambda)\,y(\lambda)=(\text{image of }\varpi'_{l_0})^{E_0}\,u(\lambda)$ holds, together with the four normalisations: whenever $x(\lambda)$ lies in $C^{\mathrm{Ig}}_\lambda.\mathrm{integers}$ its residue is $0$; whenever it lies in $R^{\mathrm{SS}}_s.\mathrm{integers}$ its residue has order $1$ at $x_t(\lambda)$; whenever $y(\lambda)$ lies in $R^{\mathrm{SS}}_s.\mathrm{integers}$ its residue is $0$; whenever it lies in $C^{\mathrm{Ig}}_\lambda.\mathrm{integers}$ its residue has order $1$ at $x_s(\lambda,s)$;
--   — every $f$ in `fieldBar q M'` is a quotient of elements of some $\mathcal{N}_{0,\lambda,l}$ (there are $l$ and $a,b\in\mathcal{N}_{0,\lambda,l}$ with $b\neq0$ and $fb=a$), and also a quotient by a non-zero $b\in\mathcal{N}_{0,\lambda,l_0}$ of a finite $\overline{\mathbb{Q}}$-linear combination of elements of $\mathcal{N}_{0,\lambda,l_0}$;
--   — and for every $l$: $\mathcal{N}_{0,\lambda,l_0}\subseteq\mathcal{N}_{0,\lambda,l}\subseteq\mathcal{N}_\lambda$; a place $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ lies in $\mathrm{An}(\lambda).\mathrm{dom}$ if and only if $\mathcal{N}_{0,\lambda,l}$ is contained in its valuation subring and every non-unit of $\mathcal{N}_{0,\lambda,l}$ has $P$-value in the maximal ideal of $A$; the constants from $C'_l$ lie in $\mathcal{N}_{0,\lambda,l}$; every element of $\mathcal{N}_{0,\lambda,l}$ differs from such a constant by a non-unit; families of elements of $\mathcal{N}_{0,\lambda,l}$ combined with $C'_l$-linearly independent coefficients from $\overline{\mathbb{Q}}$ can vanish only trivially; there is a subring $B$ of `fieldBar q M'` inside $\mathcal{N}_{0,\lambda,l}$ containing $x(\lambda),y(\lambda),u(\lambda)$ such that $\mathcal{N}_{0,\lambda,l}$ consists of the quotients $g/h$ with $g,h\in B$ and $h$ a unit of $\mathcal{N}_{0,\lambda,l}$, and $B$ is generated as a subring by the constants from $C'_l$ together with a finite set; $x(\lambda),y(\lambda)\in\mathcal{N}_{0,\lambda,l}$ and $u(\lambda)$ is a unit of it; and finally there are a ring homomorphism $\sigma\colon W_l\to$ the adic completion of $\mathcal{N}_{0,\lambda,l}$ at its maximal ideal, and a ring isomorphism $\iota$ from that completion onto the crossing model $\mathrm{UVCrossingModel}(W_l,\pi_l^{E(l)})=W_l[[U,V]]/(UV-\pi_l^{E(l)})$, such that $\sigma(\pi_l)$ is the image of $\varpi'_l$ whenever that constant lies in $\mathcal{N}_{0,\lambda,l}$, $\iota\circ\sigma$ is the constant embedding, every constant from $C'_l$ lying in $\mathcal{N}_{0,\lambda,l}$ is in the image of $\sigma$, and the two node-coordinate laws hold: if $f\in\mathcal{N}_{0,\lambda,l}$ lies in $C^{\mathrm{Ig}}_\lambda.\mathrm{integers}$ with non-zero residue of order $n$ at $x_s(\lambda,s)$, then $\iota(f)-\gamma V^{n}$ lies in the ideal generated by $\mathrm{const}(\pi_l)$ and $U$ for some unit $\gamma$ of the model, and symmetrically, if $f$ lies in $R^{\mathrm{SS}}_s.\mathrm{integers}$ with non-zero residue of order $n$ at $x_t(\lambda)$, then $\iota(f)-\gamma U^{n}$ lies in the ideal generated by $\mathrm{const}(\pi_l)$ and $V$ for some unit $\gamma$.
--
--   Ninthly, a moduli (Hasse) clause for the invariant $J$: there are an element $J$ of `fieldBar q M'` whose Laurent series is [`ModularCurve.jqNModC (AlgebraicClosure ℚ) q`](def/ModularCurve_JqCoeff.html#L18), an element $a_0\in A$, and a proof that $J-a_0$ lies in $R^{\mathrm{SS}}_s.\mathrm{integers}$, such that its $R^{\mathrm{SS}}_s$-residue is $0$; the residue of $a_0$ in $\mathrm{ResidueField}\,A$ satisfies $\bar a_0^{\,q}=s.\mathrm{evalAt}(\mathtt{jGeomGen}(\mathrm{ResidueField}\,A,M'))$; and there is $c'\in\overline{\mathbb{Q}}$ with $c'(J-a_0)\in R^{\mathrm{SS}}_s.\mathrm{integers}$ of non-zero residue such that, for every point $\lambda$, $J-a_0$ lies in $C^{\mathrm{Ig}}_\lambda.\mathrm{integers}$ with non-zero residue and $\mathrm{ord}_{x_t(\lambda)}$ of the residue of $c'(J-a_0)$ equals $-\mathrm{ord}_{x_s(\lambda,s)}$ of the residue of $J-a_0$.
--
--   Tenthly, a family of residue discs. There are maps $\mathrm{disc}$ from places of $F^{\mathrm{SS}}_s$ to sets of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$ and $\mathrm{coord}$ from places of $F^{\mathrm{SS}}_s$ to `fieldBar q M'` such that: $(\mathrm{disc},\mathrm{coord})$ is a `DiscFamily` for $R^{\mathrm{SS}}_s$ with exceptional set the finite image of $x_t$ (each $Q$ outside that set has $\mathrm{disc}\,Q$ a residue disc with coordinate $\mathrm{coord}\,Q$, and discs attached to distinct such $Q$ are disjoint); for every $\tau$ in the subgroup generated by the automorphisms `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$ and every proof that $\tau$ preserves $R^{\mathrm{SS}}_s.\mathrm{integers}$, the induced residue automorphism `resAut` stabilises the range of $x_t$, and for $Q$ outside that range the translated disc `smulDisc τ (disc Q)` equals $\mathrm{disc}$ of the translate of $Q$; no place of any $\mathrm{An}'(\lambda).\mathrm{dom}$ lies in a disc $\mathrm{disc}\,Q$ with $Q$ outside the range of $x_t$; for every semilinear $g$ as in the first conjunct and every compatible $\varphi$ which moreover preserves the range of $x_t$, and for $Q$ outside that range, $P\in\mathrm{disc}\,Q\iff g\cdot P\in\mathrm{disc}(\varphi\cdot Q)$ for every place $P$; every $P$ in such a disc satisfies $0\le P.\mathrm{ord}$ of the image of the base-changed $j$-expansion; and, finally, the discs together with the annuli cover the supersingular tube of $s$: every rational place $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ which satisfies the tube condition of the sixth conjunct (for all $f\in R_0.\mathrm{integers}$ integral wherever the $j$-expansion is and with $R_0$-residue in the valuation subring of $s$, and all $a\in A$ with residue the value of $s$ at that residue, $P.\mathrm{evalAt}(f)-a$ lies in the maximal ideal of $A$) either lies in $\mathrm{disc}\,Q$ for some $Q$ outside the range of $x_t$, or lies in $\mathrm{An}'(\lambda).\mathrm{dom}$ for some point $\lambda$.
--
--   This is the local description, at a single supersingular place $s$ of the characteristic-$q$ modular function field, of the semistable model of the modular curve of level $q^2M'$ in the case $q=3$ and at an auxiliary rigid level provided by the prime $\ell\equiv 11\pmod{12}$ dividing $M'$: the $q+1$ Igusa components meeting above $s$ are joined to the Drinfeld side by two-ended tube annuli with common domain and reciprocal parameters, the crossings are presented by $UV=\pi^{E}$ models over complete discrete valuation rings, and the rest of the tube is covered by a Galois-equivariant family of residue discs. It feeds the construction of the full semistable covering in [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_tubeAnnuli_width_inertia_discs_charted_inertNodes_nodeRings_nodeCharts_moduliHasse_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open scoped Classical in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_tubeAnnuli_width_inertia_discs_charted_inertNodes_nodeRings_nodeCharts_moduliHasse_of_eq_three_of_dvd
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
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))
    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hSS : ∀ s' : ↥W, OSS s' ∈ {O : ValuationSubring (fieldBar q M') |
      (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A) ∧
      (∃ t : fieldBar q M', t ∈ O ∧ ∀ a : A,
        ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O, IsUnit (⟨_, h⟩ : O)) ∧
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          (IntermediateField.inclusion hle f : fieldBar q M') ∈ O ∧
          ∀ a : A, residue A a =
              (s' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
                - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O,
              (⟨_, h⟩ : O) ∈ maximalIdeal O) ∧
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → O.comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = O)})

    (FIg : CuspidalType.ProjLine q → Type) [∀ ℓ, Field (FIg ℓ)] [∀ ℓ, Algebra (ResidueField A) (FIg ℓ)]
    (FSS : ↥W → Type) [∀ s, Field (FSS s)] [∀ s, Algebra (ResidueField A) (FSS s)]
    (CIg : ∀ ℓ, ComponentChart A (fieldBar q M') (FIg ℓ)) (hCIg : ∀ ℓ, (CIg ℓ).integers = OIg ℓ)
    (RSS : ∀ s, RegularProlongation A (fieldBar q M') (FSS s)) (hRSS : ∀ s, (RSS s).integers = OSS s)

    (CSS : ∀ s, ComponentChart A (fieldBar q M') (FSS s)) (hCSS : ∀ s, (CSS s).integers = OSS s)
    (xs : ∀ ℓ : CuspidalType.ProjLine q, ↥W → Place (ResidueField A) (FIg ℓ))
    (hxs_mem : ∀ ℓ s, xs ℓ s ∈ (CIg ℓ).nodes)
    (hxs_over : ∀ ℓ, ∃ j : modularFunctionFieldC (ResidueField A) M' →+* FIg ℓ,
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ (CIg ℓ).integers,
          (CIg ℓ).residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
      ∀ (s : ↥W) (g : modularFunctionFieldC (ResidueField A) M'),
        g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
          j g ∈ (xs ℓ s).toValuationSubring)
    (πt : AlgebraicClosure ℚ) (hπt : πt ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπA : πt ∈ A)
    (s : ↥W) :
    ∃ (An An' : CuspidalType.ProjLine q → Annulus A (fieldBar q M'))
      (xt : CuspidalType.ProjLine q → Place (ResidueField A) (FSS s)),

      (∀ g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'),
        (∀ x : AlgebraicClosure ℚ, SemilinearAut.baseAut g x ∈ A ↔ x ∈ A) →
        (∀ x : ↥A, ∃ h : SemilinearAut.baseAut g (x : AlgebraicClosure ℚ) ∈ A, (⟨_, h⟩ : ↥A) - x ∈ maximalIdeal ↥A) →

        g • (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) = (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) →
        ∀ (hst : ∀ f : ↥(fieldBar q M'), f ∈ (RSS s).integers ↔ g • f ∈ (RSS s).integers)
          (φ : FSS s ≃ₐ[ResidueField A] (FSS s)),
        (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (RSS s).integers),
          (RSS s).residue ⟨g • f, (hst f).mp hf⟩ = φ ((RSS s).residue ⟨f, hf⟩)) →
        ∀ Q : Place (ResidueField A) (FSS s), φ • Q ∈ Set.range xt ↔ Q ∈ Set.range xt) ∧

      (∀ ℓ, (An' ℓ).dom = (An ℓ).dom ∧ (An' ℓ).modulus = (An ℓ).modulus ∧
        ((An ℓ).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (∃ w : ℕ, 1 ≤ w ∧ ∃ u : Aˣ, (An ℓ).modulus = u * ⟨πt, hπA⟩ ^ w) ∧

        (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 →
          let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
          (∀ P, P ∈ (An ℓ).dom ↔ g • P ∈ (An ℓ).dom) ∧
            g • (An ℓ).param = (An ℓ).param ∧ g • (An' ℓ).param = (An' ℓ).param) ∧
        (An' ℓ).param * (An ℓ).param =
          algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((An ℓ).modulus : AlgebraicClosure ℚ)) ∧

      (∀ ℓ, (An ℓ).IsAttached (CIg ℓ) (xs ℓ s) ∧
        ∃ hz : (An' ℓ).param ∈ (RSS s).integers, (xt ℓ).ord ((RSS s).residue ⟨(An' ℓ).param, hz⟩) = 1 ∧
          ∀ (f : fieldBar q M') (hf : f ∈ (RSS s).integers), (RSS s).residue ⟨f, hf⟩ ≠ 0 →
            (∀ P ∈ (An' ℓ).dom, P.ord f = 0) →
              ∀ P ∈ (An' ℓ).dom,
                ∃ h : P.evalAt f * (P.evalAt (An' ℓ).param) ^ (-((xt ℓ).ord ((RSS s).residue ⟨f, hf⟩))) ∈ A,
                  IsUnit (⟨_, h⟩ : A)) ∧
      Function.Injective xt ∧

      (∀ ℓ ℓ' P, P ∈ (An ℓ).dom → P ∈ (An ℓ').dom → ℓ = ℓ') ∧

      (∀ ℓ, ∀ P ∈ (An ℓ).dom, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
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

      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ σ : Equiv.Perm (CuspidalType.ProjLine q),
        (∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ)) →
        ∀ ℓ, ((An ℓ).comap (levelAutBar q M' ζ' γ)).dom = (An (σ ℓ)).dom ∧ (An ℓ).modulus = (An (σ ℓ)).modulus) ∧

      (∃ (Λ : Type) (C' : Λ → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : Λ) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
        (_ : ∀ l, IsDomain ↥(C' l)) (_ : ∀ l, IsDiscreteValuationRing ↥(C' l))
        (ϖ' : ∀ l, ↥(C' l)) (l₀ : Λ)
        (Wc : Λ → Type) (_ : ∀ l, CommRing (Wc l)) (_ : ∀ l, IsDomain (Wc l)) (_ : ∀ l, IsDiscreteValuationRing (Wc l))
        (_ : ∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l))
        (π : ∀ l, Wc l) (E : Λ → ℕ) (E₀ : ℕ)
        (𝒩 : CuspidalType.ProjLine q → Subring (fieldBar q M'))
        (𝒩₀ : CuspidalType.ProjLine q → Λ → Subring (fieldBar q M'))
        (hloc : ∀ ℓ l, IsLocalRing ↥(𝒩₀ ℓ l)) (hnoe : ∀ ℓ l, IsNoetherianRing ↥(𝒩₀ ℓ l))
        (x y u : CuspidalType.ProjLine q → fieldBar q M'),
        (∀ (l : Λ) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d') ∧
        (∀ l, C' l₀ ≤ C' l) ∧
        ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ≠ 0 ∧
        (∀ a : AlgebraicClosure ℚ, a ∈ A → IsAlgebraic ↥(C' l₀) a) ∧
        (∀ l, Irreducible (π l)) ∧ (∀ l, 1 ≤ E l) ∧
        (∀ ℓ,

          (An ℓ).param = y ℓ ∧
          ((An ℓ).modulus : AlgebraicClosure ℚ) = ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ ∧

          (xs ℓ s).IsRational ∧ (xt ℓ).IsRational ∧ (∀ P ∈ (An ℓ).dom, P.IsRational) ∧

          (∀ f : fieldBar q M', f ∈ 𝒩 ℓ ↔ f ∈ (CIg ℓ).integers ∧ f ∈ (RSS s).integers ∧ ∀ P ∈ (An ℓ).dom, f ∈ P.toValuationSubring) ∧
          (∀ f ∈ 𝒩 ℓ, ∀ P ∈ (An ℓ).dom, P.evalAt f ∈ A) ∧

          x ℓ * y ℓ = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ * u ℓ ∧
          (∀ h₁ : x ℓ ∈ (CIg ℓ).integers, (CIg ℓ).residue ⟨x ℓ, h₁⟩ = 0) ∧
          (∀ h₂ : x ℓ ∈ (RSS s).integers, (xt ℓ).ord ((RSS s).residue ⟨x ℓ, h₂⟩) = 1) ∧
          (∀ h₂ : y ℓ ∈ (RSS s).integers, (RSS s).residue ⟨y ℓ, h₂⟩ = 0) ∧
          (∀ h₁ : y ℓ ∈ (CIg ℓ).integers, (xs ℓ s).ord ((CIg ℓ).residue ⟨y ℓ, h₁⟩) = 1) ∧

          (∀ f : fieldBar q M', ∃ (l : Λ) (a b : ↥(𝒩₀ ℓ l)), (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = (a : fieldBar q M')) ∧
          (∀ f : fieldBar q M', ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ ℓ l₀)) (b : ↥(𝒩₀ ℓ l₀)),
            (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = ∑ i, c i • ((a i : ↥(𝒩₀ ℓ l₀)) : fieldBar q M')) ∧

          (∀ l, letI : IsLocalRing ↥(𝒩₀ ℓ l) := hloc ℓ l;
            𝒩₀ ℓ l₀ ≤ 𝒩₀ ℓ l ∧ 𝒩₀ ℓ l ≤ 𝒩 ℓ ∧
            (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ (An ℓ).dom ↔
              (∀ f : fieldBar q M', f ∈ 𝒩₀ ℓ l → f ∈ P.toValuationSubring) ∧
              (∀ f : ↥(𝒩₀ ℓ l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
            (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀ ℓ l) ∧
            (∀ g : ↥(𝒩₀ ℓ l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀ ℓ l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
            (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ ℓ l)), LinearIndependent ↥(C' l) c →
              ∑ i, c i • ((a i : ↥(𝒩₀ ℓ l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧

            (∃ Bx : Subring (fieldBar q M'),
              (∀ f : fieldBar q M', f ∈ Bx → f ∈ 𝒩₀ ℓ l) ∧
              x ℓ ∈ Bx ∧ y ℓ ∈ Bx ∧ u ℓ ∈ Bx ∧
              (∀ f : fieldBar q M', f ∈ 𝒩₀ ℓ l ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
                (∀ hh : h ∈ 𝒩₀ ℓ l, IsUnit (⟨h, hh⟩ : ↥(𝒩₀ ℓ l))) ∧ f * h = g) ∧
              (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
                ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
                  (↑T : Set (fieldBar q M'))))) ∧
            x ℓ ∈ 𝒩₀ ℓ l ∧ y ℓ ∈ 𝒩₀ ℓ l ∧ (∃ hu : u ℓ ∈ 𝒩₀ ℓ l, IsUnit (⟨u ℓ, hu⟩ : ↥(𝒩₀ ℓ l))) ∧
            ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l))
              (ι : AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l) ≃+* UVCrossingModel (Wc l) (π l ^ E l)),
              (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀ ℓ l,
                σ (π l) = algebraMap ↥(𝒩₀ ℓ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l)) ⟨_, h⟩) ∧
              (∀ o : Wc l, ι (σ o) = const (π l ^ E l) o) ∧
              (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀ ℓ l),
                ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀ ℓ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l)) ⟨_, h⟩) ∧
              (∀ (f : ↥(𝒩₀ ℓ l)) (n : ℕ) (h₁ : f.1 ∈ (CIg ℓ).integers), (CIg ℓ).residue ⟨f.1, h₁⟩ ≠ 0 →
                (xs ℓ s).ord ((CIg ℓ).residue ⟨f.1, h₁⟩) = (n : ℤ) →
                  ∃ γ : UVCrossingModel (Wc l) (π l ^ E l), IsUnit γ ∧
                    ι (algebraMap ↥(𝒩₀ ℓ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l)) f) - γ * V (π l ^ E l) ^ n ∈
                      Ideal.span {const (π l ^ E l) (π l), U (π l ^ E l)}) ∧
              (∀ (f : ↥(𝒩₀ ℓ l)) (n : ℕ) (h₂ : f.1 ∈ (RSS s).integers), (RSS s).residue ⟨f.1, h₂⟩ ≠ 0 →
                (xt ℓ).ord ((RSS s).residue ⟨f.1, h₂⟩) = (n : ℤ) →
                  ∃ γ : UVCrossingModel (Wc l) (π l ^ E l), IsUnit γ ∧
                    ι (algebraMap ↥(𝒩₀ ℓ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l)) f) - γ * U (π l ^ E l) ^ n ∈
                      Ideal.span {const (π l ^ E l) (π l), V (π l ^ E l)})))) ∧

      (∃ (J : ↥(fieldBar q M')) (hJ : (J : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqNModC (AlgebraicClosure ℚ) q)
          (a₀ : AlgebraicClosure ℚ) (ha₀ : a₀ ∈ A)
          (hR : J - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀ ∈ (RSS s).integers),
        (RSS s).residue ⟨_, hR⟩ = 0 ∧
        (IsLocalRing.residue ↥A ⟨a₀, ha₀⟩) ^ q =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField ↥A) M') ∧
        ∃ (c' : AlgebraicClosure ℚ) (htc : c' • (J - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀) ∈ (RSS s).integers),
          (RSS s).residue ⟨_, htc⟩ ≠ 0 ∧
          ∀ ℓ, ∃ hC : J - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀ ∈ (CIg ℓ).integers,
            (CIg ℓ).residue ⟨_, hC⟩ ≠ 0 ∧
            (xt ℓ).ord ((RSS s).residue ⟨_, htc⟩) = -((xs ℓ s).ord ((CIg ℓ).residue ⟨_, hC⟩))) ∧

      ∃ (disc : Place (ResidueField A) (FSS s) → Set (Place (AlgebraicClosure ℚ) (fieldBar q M'))) (coord : Place (ResidueField A) (FSS s) → (fieldBar q M')),
      (haveI := Fintype.ofFinite (CuspidalType.ProjLine q);
        (RSS s).DiscFamily (Finset.univ.image xt) disc coord) ∧
      (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}, ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ (RSS s).integers ↔ f ∈ (RSS s).integers)
        (Q : Place (ResidueField A) (FSS s)), (RSS s).resAut τ hτ • Q ∈ Set.range xt ↔ Q ∈ Set.range xt) ∧
      (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}, ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ (RSS s).integers ↔ f ∈ (RSS s).integers)
        (Q : Place (ResidueField A) (FSS s)), Q ∉ Set.range xt →
          RegularProlongation.smulDisc τ (disc Q) = disc ((RSS s).resAut τ hτ • Q)) ∧

      (∀ ℓ, ∀ P ∈ (An' ℓ).dom, ∀ (Q : Place (ResidueField A) (FSS s)), Q ∉ Set.range xt → P ∉ disc Q) ∧

      (∀ g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'),
        (∀ x : AlgebraicClosure ℚ, SemilinearAut.baseAut g x ∈ A ↔ x ∈ A) →
        (∀ x : ↥A, ∃ h : SemilinearAut.baseAut g (x : AlgebraicClosure ℚ) ∈ A, (⟨_, h⟩ : ↥A) - x ∈ maximalIdeal ↥A) →

        g • (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) = (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) →
        ∀ (hst : ∀ f : ↥(fieldBar q M'), f ∈ (RSS s).integers ↔ g • f ∈ (RSS s).integers)
          (φ : FSS s ≃ₐ[ResidueField A] (FSS s)),
        (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (RSS s).integers),
          (RSS s).residue ⟨g • f, (hst f).mp hf⟩ = φ ((RSS s).residue ⟨f, hf⟩)) →
        (∀ Q : Place (ResidueField A) (FSS s), φ • Q ∈ Set.range xt ↔ Q ∈ Set.range xt) →
        ∀ (Q : Place (ResidueField A) (FSS s)), Q ∉ Set.range xt →
          ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ disc Q ↔ g • P ∈ disc (φ • Q)) ∧

      (∀ Q : Place (ResidueField A) (FSS s), Q ∉ Set.range xt → ∀ P ∈ disc Q,
        0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

      ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
            ∀ a : A, residue A a =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
              ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                (⟨_, h⟩ : A) ∈ maximalIdeal A) →
        (∃ Q : Place (ResidueField A) (FSS s), Q ∉ Set.range xt ∧ P ∈ disc Q) ∨ ∃ ℓ : CuspidalType.ProjLine q, P ∈ (An' ℓ).dom := by sorry
