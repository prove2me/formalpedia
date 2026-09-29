-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/1f520edb-27bf-5aca-a5fa-6f68d41ec481
-- title:
--   Reciprocal annulus pair at each node, case q=3
-- statement:
--   Throughout, $q$ is a prime with $q = 3$ and $M'$ a non-zero natural number not divisible by $q$, and an auxiliary guard is fixed: a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$.
--
--   **Geometric frame.** $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime q`, i.e. $q$ is a non-unit of $A$; $\kappa =$ `ResidueField A`. $W$ is a finite set of places of $\kappa$-function field `modularFunctionFieldC κ M'` $= \kappa(j_q, j_{q,M'})$, the subfield of $\kappa((t))$ generated over $\kappa$ by the $q$-expansions `jqModC κ` and `jqNModC κ M'`, and `hW` says that $W$ consists exactly of the members of `ssPlaces q M' κ`, i.e. of those places $w$ which are rational (the structure map $\kappa \to w$'s residue field is surjective), satisfy `IsAffineGeomPlace κ M'`, and have `w.evalAt (jGeomGen κ M') ∈ ssJSet q κ`; $s$ is a chosen member of $W$. Here a `Place K F` is a valuation subring of $F$ containing the image of $K$, distinct from $F$ and a principal ideal ring; `ord` is minus the logarithm of its adic valuation and `evalAt f` is the value in $K$ of the residue of $f$ when $f$ is integral, $0$ otherwise.
--
--   The hypothesis `hle` records the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'` of intermediate fields of $\overline{\mathbb{Q}}((t))$: the left-hand field is $\overline{\mathbb{Q}}$ adjoined to the coefficientwise images of the full level-$M'$ modular function field, the right-hand field is `xHFunctionFieldBar (q^2 * M') (levelH q M')`, the analogous base change of the $q$-expansion function field of $\Gamma_H(q^2M')$ with $H =$ `levelH q M'` the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, that is the units congruent to $1$ modulo $q$. $R_0$ is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` onto `modularFunctionFieldC κ M'` (a valuation subring of integers meeting $\overline{\mathbb{Q}}$ exactly in $A$, a surjective residue map with kernel the maximal ideal, compatible with the residue of $A$, a scaling clause, and a degree- and divisor-compatible map on places), and `hR₀` states that $R_0$ is computed coefficientwise: for every $y \in A((t))$ whose image in $\overline{\mathbb{Q}}((t))$ lies in `modularFunctionFieldBar M'`, that image is $R_0$-integral and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$.
--
--   $\pi \in \overline{\mathbb{Q}}$ satisfies $\pi^{q^2-1} = q$ and lies in $A$. $F_{ss} =$ `FSS` is a field over $\kappa$ and $R$ a `RegularProlongation` of $A$ from `fieldBar q M'` onto $F_{ss}$ (valuation subring of integers meeting $\overline{\mathbb{Q}}$ in $A$, surjective residue onto $F_{ss}$ with kernel the maximal ideal, compatible with the residue of $A$, and the scaling clause); $N$ is a finite set of places of $F_{ss}$ over $\kappa$, the nodes. For each place $x$ of $F_{ss}$ there are a field `FIx x` over $\kappa$, a regular prolongation `Rx x` of $A$ from `fieldBar q M'` onto `FIx x`, and a place `bx x` of `FIx x` over $\kappa$.
--
--   **Layer data.** $\Lambda$ is a type, $C' : \Lambda \to$ subrings of $\overline{\mathbb{Q}}$ all contained in $A$, each a domain and a discrete valuation ring, with elements $\varpi'_l \in C'_l$ and a distinguished index $l_0$; $W_l =$ `Wc l` are complete discrete valuation rings (commutative domains, discrete valuation rings, adically complete for the maximal ideal) with elements $\pi_{W,l}$, together with exponents $E : \Lambda \to \mathbb{N}$ and $E_0 \in \mathbb{N}$. Further, $S$ assigns to each place of $F_{ss}$ a set of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$, $\mathcal{N}$ and $\mathcal{N}_0$ assign subrings $\mathcal{N}_{nd}$ and $\mathcal{N}_{nd,l}$ of `fieldBar q M'` (local by `hloc`, noetherian by `hnoe`), and $c^x, c^y, c^u$ assign to each place of $F_{ss}$ an element of `fieldBar q M'`.
--
--   **The hypothesis `hnodes`.** It is the conjunction of the following clauses.
--
--   *Layer laws.* For every $l$ and $d \in C'_l$, the residue of $d$ in $A$ vanishes precisely when $\varpi'_l \mid d$ in $C'_l$; $C'_{l_0} \le C'_l$ for all $l$; $\varpi'_{l_0} \neq 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_{W,l}$ is irreducible and $1 \le E_l$. Moreover $\varpi'_{l_0}$ is fixed by every $\tau$ in `A.inertiaSubgroupIn ℚ` (the image in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ inside its decomposition subgroup) with `A.tameCharacter π τ = 1`, the tame character being the residue of $\tau(\pi)/\pi$ when that quotient lies in $A$ and $0$ otherwise; and there are $w \ge 1$ and a unit $v$ of $A$ with $(\varpi'_{l_0})^{E_0} = v\,\pi^{w}$ in $A$.
--
--   *Per-node clauses,* for every $nd \in N$: the places `bx nd`, $nd$ and all $P \in S_{nd}$ are rational; $\mathcal{N}_{nd}$ consists exactly of those $f$ that are `Rx nd`-integral, $R$-integral and integral at every $P \in S_{nd}$; for $f \in \mathcal{N}_{nd}$ and $P \in S_{nd}$ one has $P.\mathrm{evalAt}\,f \in A$. The node equation $c^x_{nd}\,c^y_{nd} = (\varpi'_{l_0})^{E_0} c^u_{nd}$ holds in `fieldBar q M'`, together with the four end laws: the `Rx nd`-residue of $c^x_{nd}$ is $0$; the order at $nd$ of the $R$-residue of $c^x_{nd}$ is $1$; the $R$-residue of $c^y_{nd}$ is $0$; the order at `bx nd` of the `Rx nd`-residue of $c^y_{nd}$ is $1$ (each stated conditionally on the relevant integrality). For every $\tau$ in `A.inertiaSubgroupIn ℚ` with trivial tame character, the semilinear automorphism $g$ of `fieldBar q M'` obtained from $\tau$ by [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) (coefficientwise action on Laurent series) preserves $S_{nd}$ as a set of places and fixes $c^x_{nd}$ and $c^y_{nd}$.
--
--   Generation: every $f \in$ `fieldBar q M'` satisfies $f b = a$ for some $l$ and some $a, b \in \mathcal{N}_{nd,l}$ with $b \neq 0$; and over the base layer, every $f$ satisfies $f b = \sum_{i<n} c_i a_i$ with $c_i \in \overline{\mathbb{Q}}$, $a_i, b \in \mathcal{N}_{nd,l_0}$, $b \neq 0$.
--
--   Per layer $l$: $\mathcal{N}_{nd,l_0} \le \mathcal{N}_{nd,l} \le \mathcal{N}_{nd}$; $S_{nd}$ is exactly the set of places $P$ at which $\mathcal{N}_{nd,l}$ is integral and at which every non-unit $f$ of $\mathcal{N}_{nd,l}$ has $P.\mathrm{evalAt}\,f$ in the maximal ideal of $A$; the image of $C'_l$ lies in $\mathcal{N}_{nd,l}$; every $g \in \mathcal{N}_{nd,l}$ differs from the image of some element of $C'_l$ by a non-unit; for $c : \mathrm{Fin}\,n \to \overline{\mathbb{Q}}$ linearly independent over $C'_l$ and $a : \mathrm{Fin}\,n \to \mathcal{N}_{nd,l}$, the relation $\sum_i c_i a_i = 0$ forces all $a_i = 0$; $c^x_{nd}, c^y_{nd} \in \mathcal{N}_{nd,l}$ and $c^u_{nd}$ is a unit of $\mathcal{N}_{nd,l}$. Finally there are a ring homomorphism $\sigma$ from $W_l$ to the adic completion of $\mathcal{N}_{nd,l}$ at its maximal ideal and a ring isomorphism $\iota$ of that completion with `UVCrossingModel (Wc l) (πW l ^ E l)` $= W_l[[U,V]]/(UV - \pi_{W,l}^{E_l})$ (formal power series in two variables modulo that relation) such that: $\sigma(\pi_{W,l})$ is the image of $\varpi'_l$ whenever the latter lies in $\mathcal{N}_{nd,l}$; $\iota \circ \sigma$ is the constant map `const`; every element of $C'_l$ whose image lies in $\mathcal{N}_{nd,l}$ is in the image of $\sigma$; and the two crossing laws: for $f \in \mathcal{N}_{nd,l}$ with non-zero `Rx nd`-residue of order $n$ at `bx nd` there is a unit $\gamma$ with $\iota(f) - \gamma V^{n}$ in the ideal generated by `const (πW l)` and $U$, and for $f$ with non-zero $R$-residue of order $n$ at $nd$ there is a unit $\gamma$ with $\iota(f) - \gamma U^{n}$ in the ideal generated by `const (πW l)` and $V$.
--
--   *Disjointness.* For $nd, nd' \in N$, if some place lies in both $S_{nd}$ and $S_{nd'}$ then $nd = nd'$.
--
--   *Tube clause.* For $nd \in N$, $P \in S_{nd}$ and $R_0$-integral $f$ in `modularFunctionFieldBar M'` such that $f$ has non-negative order at every place of `modularFunctionFieldBar M'` at which the element `coeffEmb (AlgebraicClosure ℚ) jq` (the $q$-expansion of $j$, viewed in that field) has non-negative order: if the $R_0$-residue of $f$ is integral at $s$, then for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference $P.\mathrm{evalAt}(f) - a$ lies in $A$ and in its maximal ideal, $f$ being transported along the inclusion `hle`.
--
--   *Level equivariance.* For every $\zeta' \in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in SL(2,\mathbb{Z})$ lying in $\Gamma_0(M')$, there is a map $\tau_N$ on places of $F_{ss}$ with: $\tau_N(nd) \in N$ for $nd \in N$; for all places $P$ of `fieldBar q M'`, `levelAutBar q M' ζ' γ • P ∈ S nd` iff $P \in S_{\tau_N(nd)}$; and the pullback of `(Rx nd).integers` along `levelAutBar q M' ζ' γ` is `(Rx (τN nd)).integers`.
--
--   *Galois stability of $N$.* For every $\tau$ in the subgroup of $\mathrm{Aut}_{\overline{\mathbb{Q}}}($ `fieldBar q M'` $)$ generated by the automorphisms `levelAutBar q M' ζ' γ` with $\zeta' \in$ `Idx q` and $\gamma \in \Gamma_0(M')$, and given that $\tau$ preserves $R$-integrality, for $nd \in N$ the place `R.resAut τ hτ • nd` lies in $N$ and `smulDisc τ (S nd)` $= \{P \mid \tau^{-1}\cdot P \in S_{nd}\}$ equals $S$ at that place.
--
--   *Compatibility of $R_0$ with the ends.* For $nd \in N$, every $R_0$-integral $f$ becomes `Rx nd`-integral under the inclusion; and there is a ring homomorphism $j$ from `modularFunctionFieldC κ M'` to `FIx nd` carrying $R_0$-residues to `Rx nd`-residues of the included elements, and such that $g$ is integral at $s$ if and only if $j(g)$ is integral at `bx nd`.
--
--   **Conclusion.** For every $nd \in N$ there exist two annuli $\mathrm{An}, \mathrm{An}'$ of type `Annulus A (fieldBar q M')` — each consisting of a set `dom` of places, a parameter `param`, and a modulus in the maximal ideal of $A$, subject to: every $P \in$ `dom` is rational with `param` integral at $P$, $P.\mathrm{evalAt}$ `param` in the maximal ideal of $A$ and non-zero, and the modulus a multiple of it by an element of the maximal ideal; for every non-zero $c$ in the maximal ideal of $A$ dividing the modulus with quotient in the maximal ideal, a unique $P \in$ `dom` with $P.\mathrm{evalAt}$ `param` $= c$; $P.\mathrm{ord}(\mathrm{param} - P.\mathrm{evalAt}\,\mathrm{param}) = 1$ on `dom`; and a unit principle for functions of order $0$ throughout `dom` — such that:
--
--   1. a place $P$ of `fieldBar q M'` lies in $\mathrm{An}.\mathrm{dom}$ if and only if $P \in S_{nd}$;
--
--   2. $\mathrm{An}'.\mathrm{dom} = \mathrm{An}.\mathrm{dom}$ and $\mathrm{An}'.\mathrm{modulus} = \mathrm{An}.\mathrm{modulus}$;
--
--   3. the modulus equals $(\varpi'_{l_0})^{E_0}$ in $\overline{\mathbb{Q}}$, and is non-zero;
--
--   4. $\mathrm{An}.\mathrm{param} = c^y_{nd}$;
--
--   5. $\mathrm{An}'.\mathrm{param} \cdot \mathrm{An}.\mathrm{param}$ is the image of the modulus in `fieldBar q M'`;
--
--   6. $\mathrm{An}.\mathrm{param}$ is `Rx nd`-integral, the order at `bx nd` of its residue is $1$, and for every `Rx nd`-integral $f$ with non-zero residue and with $P.\mathrm{ord}\,f = 0$ at all $P \in \mathrm{An}.\mathrm{dom}$, at each such $P$ the element $P.\mathrm{evalAt}(f)\cdot (P.\mathrm{evalAt}\,\mathrm{An}.\mathrm{param})^{-m}$, where $m$ is the order at `bx nd` of the residue of $f$, lies in $A$ and is a unit there;
--
--   7. symmetrically, $\mathrm{An}'.\mathrm{param}$ is $R$-integral, the order at $nd$ of its $R$-residue is $1$, and for every $R$-integral $f$ with non-zero residue and with $P.\mathrm{ord}\,f = 0$ at all $P \in \mathrm{An}'.\mathrm{dom}$, at each such $P$ the element $P.\mathrm{evalAt}(f)\cdot (P.\mathrm{evalAt}\,\mathrm{An}'.\mathrm{param})^{-m}$, with $m$ the order at $nd$ of the residue of $f$, lies in $A$ and is a unit there;
--
--   8. two distinct radii occur: there are $P, P' \in \mathrm{An}.\mathrm{dom}$ with $A$-valuations of $P.\mathrm{evalAt}\,\mathrm{An}.\mathrm{param}$ and $P'.\mathrm{evalAt}\,\mathrm{An}.\mathrm{param}$ different;
--
--   9. $\mathrm{An}.\mathrm{modulus}$ lies in the maximal ideal of $A$ (a condition already part of the `Annulus` data).
--
--   This is the construction, at each node of the reduction under consideration, of a pair of reciprocal annuli in the level-$q^2M'$ modular function field: the domain of each annulus is exactly the set $S_{nd}$ of places attached to the node, their parameters multiply to the modulus $(\varpi'_{l_0})^{E_0}$, and each annulus is attached to one of the two branches through the node (the $\mathrm{bx}$ end for one, the $nd$ end for the other), with at least two distinct radii occurring. It is the $q = 3$ instance, under the auxiliary guard provided by the prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, and it feeds the subsequent statements on cross units at node places, on the covering of the nodes by annuli, and on the exclusion of a smooth-point package at the ends of the node charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_three_of_dvd
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
