-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/1d2a0b1e-107d-5d0c-990d-266c48344649
-- title:
--   Reciprocal annulus pair at each node place, q = 2
-- statement:
--   **Frame.** Fixed are a prime $q$ with $q = 2$; a natural number $M'$ with $M' \neq 0$ and $q \nmid M'$; a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$; a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$, in the sense that $q$ is a non-unit of $A$ (`LiesOverPrime`); and a finite set $W$ of places of the modular function field $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over the residue field $\kappa = \mathrm{ResidueField}\,A$, whose members are, by `hW`, exactly the supersingular places for $q$, i.e. the places $w$ that are rational, affine geometric, and satisfy $w.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M') \in \mathrm{ssJSet}\,q\,\kappa$; one such place $s \in W$ is selected. Further, $\mathrm{hle}$ records the inclusion $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ of intermediate fields of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$, where $\mathrm{fieldBar}\,q\,M' = \mathrm{xHFunctionFieldBar}\,(q^2M')\,(\mathrm{levelH}\,q\,M')$; $R_0$ is a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ (a valuation subring $R_0.\mathrm{integers}$ together with a surjective residue map onto the reduced field whose kernel is the maximal ideal, compatible with $A$ and its residue map, a place map preserving degrees and pushing forward divisors of functions, and the scaling property); and `hR₀` requires that for every Laurent series $y$ over $A$ whose image in $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is the coefficientwise reduction of $y$ along $A \to \kappa$. Finally $\pi \in \overline{\mathbb{Q}}$ satisfies $\pi^{q^2-1} = q$ and $\pi \in A$.
--
--   **Prolongations and node places.** $F_{\mathrm{ss}}$ is a field over $\kappa$, $R$ a regular prolongation of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $F_{\mathrm{ss}}$ (a valuation subring with surjective residue map onto $F_{\mathrm{ss}}$, kernel the maximal ideal, compatible with $A$, and satisfying the scaling property), and $N$ a finite set of places of $F_{\mathrm{ss}}$ over $\kappa$. For every place $x$ of $F_{\mathrm{ss}}$ over $\kappa$ there are given a field $F_x$ over $\kappa$, a regular prolongation $R_x$ of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $F_x$, and a place $b_x$ of $F_x$ over $\kappa$.
--
--   **Layer data.** $\Lambda$ is an index type, $C' : \Lambda \to$ subrings of $\overline{\mathbb{Q}}$ with all $C'_l$ contained in $A$ (hypothesis `hC'A`) and each $C'_l$ a discrete valuation domain, with elements $\varpi'_l \in C'_l$ and a distinguished index $l_0$; $W^{\mathrm{c}} : \Lambda \to$ complete discrete valuation domains with elements $\pi_{W,l}$; and exponents $E : \Lambda \to \mathbb{N}$, $E_0 \in \mathbb{N}$.
--
--   **Node geometry.** For each place $x$ of $F_{\mathrm{ss}}$ there are given a set $S_x$ of places of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$, a subring $\mathcal{N}_x$ of $\mathrm{fieldBar}\,q\,M'$, subrings $\mathcal{N}_{x,l}$ for $l \in \Lambda$, each local (`hloc`) and noetherian (`hnoe`), and node coordinates $c^x_{\mathrm{nd}}, c^y_{\mathrm{nd}}, c^u_{\mathrm{nd}} \in \mathrm{fieldBar}\,q\,M'$.
--
--   **The hypothesis `hnodes`.** This single conjunction comprises the following groups.
--
--   *Layer laws:* for each $l$ and $d \in C'_l$, the residue of $d$ in $\kappa$ vanishes precisely when $d \in \varpi'_l C'_l$; $C'_{l_0} \le C'_l$ for all $l$; $\varpi'_{l_0} \neq 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_{W,l}$ is irreducible; and $1 \le E_l$ for all $l$.
--
--   *Tame invariance of the base uniformiser:* every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ with $A.\mathrm{tameCharacter}\,\pi\,\tau = 1$ fixes $\varpi'_{l_0}$.
--
--   *Comparison of $\varpi'_{l_0}$ with $\pi$:* there are $w \ge 1$ and a unit $v$ of $A$ with $(\varpi'_{l_0})^{E_0} = v\,\pi^{w}$ in $A$.
--
--   *Per-node clauses,* asserted for every $\mathrm{nd} \in N$: the places $b_{\mathrm{nd}}$, $\mathrm{nd}$ and all $P \in S_{\mathrm{nd}}$ are rational; $\mathcal{N}_{\mathrm{nd}}$ consists exactly of the $f$ lying in $(R_{\mathrm{nd}}).\mathrm{integers}$, in $R.\mathrm{integers}$ and in the valuation subring of every $P \in S_{\mathrm{nd}}$; for $f \in \mathcal{N}_{\mathrm{nd}}$ and $P \in S_{\mathrm{nd}}$ the value $P.\mathrm{evalAt}\,f$ lies in $A$; the node equation $c^x_{\mathrm{nd}} c^y_{\mathrm{nd}} = (\varpi'_{l_0})^{E_0} c^u_{\mathrm{nd}}$ holds (the constant being transported by $\overline{\mathbb{Q}} \to \mathrm{fieldBar}\,q\,M'$); the four end laws, namely $(R_{\mathrm{nd}})$-residue of $c^x_{\mathrm{nd}}$ is $0$, $\mathrm{nd}.\mathrm{ord}$ of the $R$-residue of $c^x_{\mathrm{nd}}$ is $1$, the $R$-residue of $c^y_{\mathrm{nd}}$ is $0$, and $b_{\mathrm{nd}}.\mathrm{ord}$ of the $(R_{\mathrm{nd}})$-residue of $c^y_{\mathrm{nd}}$ is $1$ (each stated under the hypothesis that the element lies in the relevant ring of integers); tame invariance of the node, i.e. for $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ with trivial tame character the semilinear automorphism $g = \mathrm{arithmeticGalois}\,(\mathrm{xHFunctionField}\,(q^2M')\,(\mathrm{levelH}\,q\,M'))\,\tau$ satisfies $P \in S_{\mathrm{nd}} \iff g \cdot P \in S_{\mathrm{nd}}$ and fixes $c^x_{\mathrm{nd}}$ and $c^y_{\mathrm{nd}}$; two generation clauses, that every $f$ becomes an element of some $\mathcal{N}_{\mathrm{nd},l}$ after multiplication by a non-zero element of $\mathcal{N}_{\mathrm{nd},l}$, and that every $f$ becomes a finite $\overline{\mathbb{Q}}$-linear combination of elements of $\mathcal{N}_{\mathrm{nd},l_0}$ after multiplication by a non-zero element of $\mathcal{N}_{\mathrm{nd},l_0}$; and, for every layer $l$: $\mathcal{N}_{\mathrm{nd},l_0} \le \mathcal{N}_{\mathrm{nd},l} \le \mathcal{N}_{\mathrm{nd}}$; the characterisation of $S_{\mathrm{nd}}$ as the set of places $P$ whose valuation subring contains $\mathcal{N}_{\mathrm{nd},l}$ and which send every non-unit of $\mathcal{N}_{\mathrm{nd},l}$ into the maximal ideal of $A$; $C'_l$ maps into $\mathcal{N}_{\mathrm{nd},l}$; every $g \in \mathcal{N}_{\mathrm{nd},l}$ differs from the image of some element of $C'_l$ by a non-unit; a linear-independence clause, namely that if $c : \mathrm{Fin}\,n \to \overline{\mathbb{Q}}$ is linearly independent over $C'_l$ and $\sum_i c_i a_i = 0$ with $a_i \in \mathcal{N}_{\mathrm{nd},l}$, then all $a_i = 0$; $c^x_{\mathrm{nd}}, c^y_{\mathrm{nd}} \in \mathcal{N}_{\mathrm{nd},l}$ and $c^u_{\mathrm{nd}}$ is a unit of $\mathcal{N}_{\mathrm{nd},l}$; and the existence of a ring homomorphism $\sigma : W^{\mathrm{c}}_l \to$ the $\mathfrak{m}$-adic completion of $\mathcal{N}_{\mathrm{nd},l}$ together with a ring isomorphism $\iota$ from that completion to $\mathrm{UVCrossingModel}\,(W^{\mathrm{c}}_l)\,(\pi_{W,l}^{E_l}) = W^{\mathrm{c}}_l[[U,V]]/(UV - \pi_{W,l}^{E_l})$ such that $\sigma(\pi_{W,l})$ is the image of $\varpi'_l$ whenever the latter lies in $\mathcal{N}_{\mathrm{nd},l}$, $\iota \circ \sigma$ is the constant map $\mathrm{const}$, every element of $C'_l$ lying in $\mathcal{N}_{\mathrm{nd},l}$ is in the image of $\sigma$, and the two residue-order laws: if $f \in \mathcal{N}_{\mathrm{nd},l}$ has non-zero $(R_{\mathrm{nd}})$-residue of $b_{\mathrm{nd}}$-order $n$, then $\iota$ of the image of $f$ differs from $\gamma V^n$, for some unit $\gamma$, by an element of the ideal generated by $\mathrm{const}(\pi_{W,l})$ and $U$; and symmetrically, if $f$ has non-zero $R$-residue of $\mathrm{nd}$-order $n$, then $\iota$ of the image of $f$ differs from $\gamma U^n$, for a unit $\gamma$, by an element of the ideal generated by $\mathrm{const}(\pi_{W,l})$ and $V$.
--
--   *Node separation:* if $\mathrm{nd}, \mathrm{nd}' \in N$ and some $P$ lies in both $S_{\mathrm{nd}}$ and $S_{\mathrm{nd}'}$, then $\mathrm{nd} = \mathrm{nd}'$.
--
--   *Tube condition at $s$:* for $\mathrm{nd} \in N$, $P \in S_{\mathrm{nd}}$ and $f \in R_0.\mathrm{integers}$ such that $f$ has non-negative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the image of $\mathrm{jq}$ has non-negative order: if the $R_0$-residue of $f$ lies in the valuation subring of $s$, then for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that residue, the difference $P.\mathrm{evalAt}(f) - a$ lies in $A$ and in its maximal ideal.
--
--   *Level equivariance:* for every $\zeta' \in \mathrm{Idx}\,q$ and every $\gamma \in \Gamma_0(M')$ there is a map $\tau_N$ on places of $F_{\mathrm{ss}}$ such that for $\mathrm{nd} \in N$: $\tau_N(\mathrm{nd}) \in N$, $(\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma) \cdot P \in S_{\mathrm{nd}} \iff P \in S_{\tau_N(\mathrm{nd})}$ for all $P$, and the pullback of $(R_{\mathrm{nd}}).\mathrm{integers}$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ equals $(R_{\tau_N(\mathrm{nd})}).\mathrm{integers}$.
--
--   *Galois equivariance for $R$:* for every $\tau$ in the subgroup of $\overline{\mathbb{Q}}$-automorphisms of $\mathrm{fieldBar}\,q\,M'$ generated by the $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$, if $\tau$ preserves $R.\mathrm{integers}$, then for $\mathrm{nd} \in N$ the place $R.\mathrm{resAut}\,\tau \cdot \mathrm{nd}$ lies in $N$ and $\mathrm{smulDisc}\,\tau\,(S_{\mathrm{nd}}) = S_{R.\mathrm{resAut}\,\tau\,\cdot\,\mathrm{nd}}$.
--
--   *Compatibility of $R_0$ with the $R_x$:* for $\mathrm{nd} \in N$, the inclusion into $\mathrm{fieldBar}\,q\,M'$ of any $f \in R_0.\mathrm{integers}$ lies in $(R_{\mathrm{nd}}).\mathrm{integers}$; and there is a ring homomorphism $j : \mathrm{modularFunctionFieldC}\,\kappa\,M' \to F_{\mathrm{nd}}$ carrying $R_0$-residues to $(R_{\mathrm{nd}})$-residues and satisfying: $g$ lies in the valuation subring of $s$ if and only if $j(g)$ lies in the valuation subring of $b_{\mathrm{nd}}$.
--
--   **Conclusion.** For every $\mathrm{nd} \in N$ there exist two annuli $\mathcal{A}, \mathcal{A}'$ for $A$ in $\mathrm{fieldBar}\,q\,M'$ — each an `Annulus`, hence carrying a domain of rational places on which the parameter has value in the maximal ideal of $A$, non-zero and dividing the modulus, the unique-point property for each admissible value, the relation $P.\mathrm{ord}(\mathrm{param} - P.\mathrm{evalAt}\,\mathrm{param}) = 1$ on the domain, and the unit principle — such that:
--
--   1. $\mathcal{A}.\mathrm{dom}$ consists exactly of the places $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$ lying in $S_{\mathrm{nd}}$;
--
--   2. $\mathcal{A}'.\mathrm{dom} = \mathcal{A}.\mathrm{dom}$ and $\mathcal{A}'.\mathrm{modulus} = \mathcal{A}.\mathrm{modulus}$;
--
--   3. the modulus equals $(\varpi'_{l_0})^{E_0}$ in $\overline{\mathbb{Q}}$, and is non-zero;
--
--   4. $\mathcal{A}.\mathrm{param} = c^y_{\mathrm{nd}}$;
--
--   5. $\mathcal{A}'.\mathrm{param} \cdot \mathcal{A}.\mathrm{param}$ is the image of the modulus under $\overline{\mathbb{Q}} \to \mathrm{fieldBar}\,q\,M'$;
--
--   6. $\mathcal{A}.\mathrm{param}$ lies in $(R_{\mathrm{nd}}).\mathrm{integers}$, its residue has $b_{\mathrm{nd}}$-order $1$, and for every $f \in (R_{\mathrm{nd}}).\mathrm{integers}$ with non-zero residue and with $P.\mathrm{ord}\,f = 0$ for all $P \in \mathcal{A}.\mathrm{dom}$, and every such $P$, the element $P.\mathrm{evalAt}(f) \cdot (P.\mathrm{evalAt}\,\mathcal{A}.\mathrm{param})^{-n}$, where $n$ is the $b_{\mathrm{nd}}$-order of the residue of $f$, lies in $A$ and is a unit there;
--
--   7. symmetrically, $\mathcal{A}'.\mathrm{param}$ lies in $R.\mathrm{integers}$, its residue has $\mathrm{nd}$-order $1$, and for every $f \in R.\mathrm{integers}$ with non-zero residue and with $P.\mathrm{ord}\,f = 0$ for all $P \in \mathcal{A}'.\mathrm{dom}$, and every such $P$, the element $P.\mathrm{evalAt}(f) \cdot (P.\mathrm{evalAt}\,\mathcal{A}'.\mathrm{param})^{-n}$, with $n$ the $\mathrm{nd}$-order of the residue of $f$, lies in $A$ and is a unit there;
--
--   8. there are places $P, P' \in \mathcal{A}.\mathrm{dom}$ with $A.\mathrm{valuation}(P.\mathrm{evalAt}\,\mathcal{A}.\mathrm{param}) \neq A.\mathrm{valuation}(P'.\mathrm{evalAt}\,\mathcal{A}.\mathrm{param})$;
--
--   9. $\mathcal{A}.\mathrm{modulus}$ lies in the maximal ideal of $A$.
--
--   At a supersingular point of the modular curve in characteristic $q$, this produces from the layered crossing presentation $W_l[[U,V]]/(UV - \pi_{W,l}^{E_l})$ of each node the pair of mutually reciprocal annuli whose common domain is the tube of places above that node, with the two ends attached to the two regular prolongations and with at least two distinct radii occurring. It is the case $q = 2$, under the rigidity guard provided by a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, and it feeds the downstream construction of cross units at node places, the covering of the semistable model by node annuli and charts, and the exclusion of smooth-point behaviour at the ends of the node charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_two_of_dvd.lean

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

open ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_two_of_dvd
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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (N : Finset (Place (ResidueField ↥A) FSS))

    (FIx : Place (ResidueField A) FSS → Type) [∀ x, Field (FIx x)] [∀ x, Algebra (ResidueField A) (FIx x)]
    (Rx : ∀ x : Place (ResidueField A) FSS, RegularProlongation A (fieldBar q M') (FIx x))
    (bx : ∀ x : Place (ResidueField A) FSS, Place (ResidueField A) (FIx x))

    (Λ : Type) (C' : Λ → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : Λ) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
    [∀ l, IsDomain ↥(C' l)] [∀ l, IsDiscreteValuationRing ↥(C' l)]
    (ϖ' : ∀ l, ↥(C' l)) (l₀ : Λ)
    (Wc : Λ → Type) [∀ l, CommRing (Wc l)] [∀ l, IsDomain (Wc l)] [∀ l, IsDiscreteValuationRing (Wc l)]
    [∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l)]
    (πW : ∀ l, Wc l) (E : Λ → ℕ) (E₀ : ℕ)

    (S : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
    (𝒩 : Place (ResidueField A) FSS → Subring (fieldBar q M'))
    (𝒩₀ : Place (ResidueField A) FSS → Λ → Subring (fieldBar q M'))
    (hloc : ∀ nd l, IsLocalRing ↥(𝒩₀ nd l)) (hnoe : ∀ nd l, IsNoetherianRing ↥(𝒩₀ nd l))
    (cx cy cu : Place (ResidueField A) FSS → fieldBar q M')
    (hnodes :

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
          (∀ nd ∈ N, ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ (Rx nd).integers) ∧
          (∀ nd ∈ N, ∃ j : modularFunctionFieldC (ResidueField A) M' →+* FIx nd,
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ (Rx nd).integers,
                (Rx nd).residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
            ∀ g : modularFunctionFieldC (ResidueField A) M',
              g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
                j g ∈ (bx nd).toValuationSubring)) :
    ∀ nd ∈ N, ∃ An An' : Annulus A ↥(fieldBar q M'),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ An.dom ↔ P ∈ S nd) ∧
      An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      (((An.modulus : ↥A) : AlgebraicClosure ℚ) = ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀) ∧ (((An.modulus : ↥A) : AlgebraicClosure ℚ) ≠ 0) ∧
      An.param = cy nd ∧
      An'.param * An.param = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((An.modulus : ↥A) : AlgebraicClosure ℚ) ∧

      (∃ hz : An.param ∈ (Rx nd).integers, (bx nd).ord ((Rx nd).residue ⟨An.param, hz⟩) = 1 ∧
        ∀ (f : ↥(fieldBar q M')) (hf : f ∈ (Rx nd).integers), (Rx nd).residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
          ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-((bx nd).ord ((Rx nd).residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

      (∃ hz : An'.param ∈ R.integers, nd.ord (R.residue ⟨An'.param, hz⟩) = 1 ∧
        ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord f = 0) →
          ∀ P ∈ An'.dom,
            ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(nd.ord (R.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

      (∃ P ∈ An.dom, ∃ P' ∈ An.dom, A.valuation (P.evalAt An.param) ≠ A.valuation (P'.evalAt An.param)) ∧

      ((An.modulus : ↥A) ∈ maximalIdeal ↥A) := by sorry
