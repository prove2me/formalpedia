-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_crossUnit_nodePlaces_of_sep
-- name    : ModularCurve.FullLevel.supersingularProlongation_exists_crossUnit_nodePlaces_of_sep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/e01925e8-8a79-5cb9-9cb8-bf3c8aabede4
-- title:
--   Cross-units separating two nodes on the supersingular fibre
-- statement:
--   Fix a prime $q$ with $5 \le q$ and a positive integer $M'$ with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$; write $\kappa =$ `ResidueField A` for its residue field. Throughout, a place of $F$ over $K$ (`Place K F`) is a valuation subring of $F$ containing the image of $K$, different from $F$ and with principal ideals; `ord` is the associated normalised integer valuation, `IsRational` means that $K$ surjects onto the residue field of the place, and `evalAt` is the resulting $K$-valued evaluation (zero outside the valuation subring). `fieldBar q M'` denotes the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $\Gamma_H(q^2M')$ for $H =$ `levelH q M'`, and `modularFunctionFieldBar M'` the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field; `modularFunctionFieldC κ M'` is the field generated over $\kappa$ by the $j$- and $j_{M'}$-expansions.
--
--   The data on the level-$M'$ side are: a finite set $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$ which (`hW`) consists exactly of the supersingular places, i.e. the rational places that are affine geometric and whose value on the geometric $j$-coordinate lies in the supersingular $j$-set of $\kappa$ for $q$; a containment `hle` of `modularFunctionFieldBar M'` in `fieldBar q M'`; a constant reduction $R_0$ of $A$ on `modularFunctionFieldBar M'` with reduced field `modularFunctionFieldC κ M'` (a valuation subring $R_0.\mathrm{integers}$, a surjective residue map onto the reduced field with kernel the maximal ideal, compatible with $A$ and its residue field, satisfying the scaling and divisor-transport axioms of `ConstantReduction`); the hypothesis `hR₀` that $R_0$ computes reductions coefficientwise on Laurent series with coefficients in $A$; a chosen element $s \in W$; and an element $\pi \in A$ with $\pi^{q^2-1} = q$.
--
--   On the full-level side there are a field $F_{ss}$ over $\kappa$ and a regular prolongation $R$ of $A$ to `fieldBar q M'` with reduced field $F_{ss}$ (valuation subring, surjective residue map with kernel the maximal ideal, compatible with $A$, and the scaling axiom of `RegularProlongation`), a finite set $N$ of places of $F_{ss}$ over $\kappa$, and, indexed by the places $Q$ of $F_{ss}$ over $\kappa$, subrings $S_Q \subseteq$ `fieldBar q M'`, ring maps $\varphi_Q : A[T] \to S_Q$ and $\chi_{0,Q} : S_Q \to \kappa$, and sets $D_Q$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$. These are constrained by: `h0`, that $F_{ss}$ contains an element transcendental over $\kappa$; `h1`, that for $f \in R_0.\mathrm{integers}$ regular wherever the $j$-expansion is regular and with $R_0$-residue in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` is $R$-integral with $R$-residue the image in $F_{ss}$ of the value of the $R_0$-residue at $s$; `h2`, that $R.\mathrm{integers}$ is preserved by the automorphisms `levelAutBar q M' ζ γ` for $\zeta$ in `Idx q` and $\gamma \in \Gamma_0(M')$; `hcard`, that $N$ has $q+1$ elements; `hpkg`, a smooth-point package of fourteen clauses (summarised here) for every place $Q \notin N$, asserting that $S_Q$ contains the image of $A$, that $\varphi_Q$ is formally smooth and formally unramified and sends constants to constants, that $\chi_{0,Q}$ restricted to constants is the residue map of $A$ and kills $\varphi_Q(T)$, that each element of the maximal ideal of $A$ is the value at $\varphi_Q(T)$ of a unique $A$-point of $S_Q$ lifting $\chi_{0,Q}$, that every element of $S_Q$ is $R$-integral with $R$-residue in the valuation subring of $Q$ reducing to its image under $\chi_{0,Q}$, that the $R$-residue of $\varphi_Q(T)$ has order $1$ at $Q$, that $D_Q$ is exactly the set of rational places at which $S_Q$ is integral with values in $A$ and at which the values of absolute value less than $1$ are those of the kernel of $\chi_{0,Q}$, that $A$-points of $S_Q$ lifting $\chi_{0,Q}$ correspond bijectively to places in $D_Q$ via evaluation, that for $P \in D_Q$ the valuation subring of $P$ consists of the fractions of elements of $S_Q$ with non-vanishing denominator, that a non-zero function with order $0$ at all places of $D_Q$ becomes a unit of $S_Q$ after multiplication by a non-zero constant, and that an $R$-integral function integral at all places of $D_Q$ lies in $S_Q$; `hdisj`, that the sets $D_Q$ for distinct $Q \notin N$ are disjoint; `hcusp`, that the image of the $j$-expansion has non-negative order at every place of every $D_Q$ with $Q \notin N$; and `heqv`, that for every $\tau$ in the subgroup generated by the level automorphisms which preserves $R.\mathrm{integers}$, the induced residue automorphism `R.resAut` preserves $N$ and transports the discs, `smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q)` for $Q \notin N$.
--
--   The node data consist of: fields $F_x$ over $\kappa$ with regular prolongations $R_x$ of $A$ to `fieldBar q M'` onto $F_x$ and places $b_x$ of $F_x$ over $\kappa$, one for each place $x$ of $F_{ss}$; an index type $\Lambda$ with subrings $C'_l \subseteq \overline{\mathbb{Q}}$ contained in $A$, each a discrete valuation domain, with elements $\varpi'_l$ and a base index $l_0$; coefficient rings $W_l$, complete discrete valuation domains, with elements $\pi_{W,l}$, exponents $E_l$ and a further exponent $E_0$; and, indexed by the places of $F_{ss}$, sets $S_x$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$, subrings $\mathcal{N}_x$ and $\mathcal{N}_{0,x,l}$ of `fieldBar q M'` (local and Noetherian by `hloc`, `hnoe`), and elements $c^x_{\mathrm{x}}, c^x_{\mathrm{y}}, c^x_{\mathrm{u}}$ of `fieldBar q M'`.
--
--   The hypothesis `hnodes` is a long conjunction, whose groups are the following. Constant-layer conditions: $\varpi'_l$ cuts out the kernel of the residue map of $A$ on $C'_l$; $C'_{l_0} \subseteq C'_l$ for all $l$; $\varpi'_{l_0} \neq 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_{W,l}$ is irreducible and $1 \le E_l$; $\varpi'_{l_0}$ is fixed by every element of the inertia subgroup of $A$ over $\mathbb{Q}$ on which the tame character attached to $\pi$ is trivial; and $(\varpi'_{l_0})^{E_0} = v\,\pi^{w}$ in $A$ for some unit $v$ of $A$ and some $w \ge 1$. Node-by-node conditions, for each $nd \in N$: rationality of $b_{nd}$, of $nd$ and of all places in $S_{nd}$; the description of $\mathcal{N}_{nd}$ as the functions that are $R_{nd}$-integral, $R$-integral and integral at all places of $S_{nd}$, with values in $A$ at those places; the crossing relation $c^{nd}_{\mathrm{x}} c^{nd}_{\mathrm{y}} = (\varpi'_{l_0})^{E_0} c^{nd}_{\mathrm{u}}$; the reduction behaviour of the two node coordinates ($R_{nd}$-residue of $c^{nd}_{\mathrm{x}}$ zero, $R$-residue of $c^{nd}_{\mathrm{x}}$ of order $1$ at $nd$, $R$-residue of $c^{nd}_{\mathrm{y}}$ zero, $R_{nd}$-residue of $c^{nd}_{\mathrm{y}}$ of order $1$ at $b_{nd}$); invariance of $S_{nd}$, $c^{nd}_{\mathrm{x}}$ and $c^{nd}_{\mathrm{y}}$ under the arithmetic Galois action of the elements of the inertia subgroup with trivial tame character; generation of `fieldBar q M'` by fractions from the rings $\mathcal{N}_{0,nd,l}$, and by $\overline{\mathbb{Q}}$-linear combinations of fractions from the base layer $\mathcal{N}_{0,nd,l_0}$; and, for each $l$, the layer conditions $\mathcal{N}_{0,nd,l_0} \subseteq \mathcal{N}_{0,nd,l} \subseteq \mathcal{N}_{nd}$, the characterisation of $S_{nd}$ as the places at which $\mathcal{N}_{0,nd,l}$ is integral and at which non-units take values in the maximal ideal of $A$, the presence of the constants $C'_l$ in $\mathcal{N}_{0,nd,l}$ together with an approximation clause (every element differs from a constant by a non-unit) and a $C'_l$-linear independence clause, membership of $c^{nd}_{\mathrm{x}}, c^{nd}_{\mathrm{y}}$ and unit-ness of $c^{nd}_{\mathrm{u}}$ in $\mathcal{N}_{0,nd,l}$, and the existence of a ring map $\sigma : W_l \to \widehat{\mathcal{N}_{0,nd,l}}$ and an isomorphism $\iota$ of the adic completion $\widehat{\mathcal{N}_{0,nd,l}}$ with the crossing model `UVCrossingModel (Wc l) (πW l ^ E l)`, that is $W_l[[U,V]]/(UV - \pi_{W,l}^{E_l})$, such that $\sigma(\pi_{W,l})$ is $\varpi'_l$, $\iota \circ \sigma$ is the constant map, the constants of $C'_l$ lying in the ring come from $W_l$ through $\sigma$, and the two branch-order clauses hold: an element whose $R_{nd}$-residue is non-zero of order $n$ at $b_{nd}$ is congruent to a unit times $V^n$ modulo the ideal generated by $\pi_{W,l}$ and $U$, and an element whose $R$-residue is non-zero of order $n$ at $nd$ is congruent to a unit times $U^n$ modulo the ideal generated by $\pi_{W,l}$ and $V$. Finally `hnodes` requires: disjointness of the sets $S_{nd}$ for distinct $nd \in N$; compatibility at the places of $S_{nd}$ with the reduction $R_0$ at $s$ (for $f \in R_0.\mathrm{integers}$ regular wherever the $j$-expansion is regular and with $R_0$-residue in the valuation subring of $s$, and for $a \in A$ whose residue is the value at $s$ of that $R_0$-residue, the difference of $P.\mathrm{evalAt}$ of the image of $f$ and $a$ lies in the maximal ideal of $A$); that each level automorphism `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$ is realised by a self-map $\tau_N$ of the places preserving $N$, transporting the sets $S_{nd}$ and the integer rings of the $R_{nd}$; that every $\tau$ in the subgroup generated by the level automorphisms preserving $R.\mathrm{integers}$ satisfies `R.resAut τ hτ • nd ∈ N` and `smulDisc τ (S nd) = S (R.resAut τ hτ • nd)` for $nd \in N$; that the image of $R_0.\mathrm{integers}$ is $R_{nd}$-integral for each $nd \in N$; and that for each $nd \in N$ there is a ring map $j$ from `modularFunctionFieldC κ M'` to $F_{nd}$ carrying $R_0$-residues to $R_{nd}$-residues and pulling back the valuation subring of $b_{nd}$ to that of $s$.
--
--   The last hypothesis `hSEP2` is the two-node separation input: for all $x, x' \in N$ with $x \neq x'$ there is $g \in$ `fieldBar q M'` lying in $\mathcal{N}_{0,x,l_0}$ and in $\mathcal{N}_{0,x',l_0}$, such that $c^x_{\mathrm{x}}$ also lies in $\mathcal{N}_{0,x,l_0}$, $g$ equals $c^x_{\mathrm{x}}$ times a unit of $\mathcal{N}_{0,x,l_0}$, and $g$ is a unit of $\mathcal{N}_{0,x',l_0}$.
--
--   Under these hypotheses the conclusion is: for all $x, x' \in N$ with $x \neq x'$ there exist $g \in$ `fieldBar q M'` and a proof that $g \in R.\mathrm{integers}$ such that (i) the $R$-residue of $g$ is non-zero; (ii) the order of that residue at $x$ is non-zero; (iii) $g$ has order $0$ at every place $P \in S_x$; and (iv) at every place $P \in S_{x'}$ the element $g$ lies in the valuation subring of $P$ and its value $P.\mathrm{evalAt}\,g$ lies in $A$ and is a unit there.
--
--   This is the cross-unit step in the construction of the semistable reduction of the full-level modular curve $X_H(q^2M')$ above a supersingular point: for each ordered pair of distinct nodes of the special fibre it produces a single function that has a zero or pole along the branch through the first node, is zero- and pole-free on the node tube there, and takes unit values on the node tube at the second node, so the two node annuli can be told apart. It feeds the aggregation of node annuli, node presentations and node charts for the supersingular fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_exists_crossUnit_nodePlaces_of_sep.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_exists_crossUnit_nodePlaces_of_sep
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
                j g ∈ (bx nd).toValuationSubring))

    (hSEP2 : (∀ x ∈ N, ∀ x' ∈ N, x ≠ x' →
            ∃ (g : ↥(fieldBar q M')) (hgx : g ∈ 𝒩₀ x l₀) (hcx : cx x ∈ 𝒩₀ x l₀) (hgx' : g ∈ 𝒩₀ x' l₀),
              (∃ u : (↥(𝒩₀ x l₀))ˣ, (⟨g, hgx⟩ : ↥(𝒩₀ x l₀)) = ⟨cx x, hcx⟩ * (u : ↥(𝒩₀ x l₀))) ∧
              IsUnit (⟨g, hgx'⟩ : ↥(𝒩₀ x' l₀)))) :
          (∀ x ∈ N, ∀ x' ∈ N, x ≠ x' →
            ∃ (g : ↥(fieldBar q M')) (hg : g ∈ R.integers), R.residue ⟨g, hg⟩ ≠ 0 ∧ x.ord (R.residue ⟨g, hg⟩) ≠ 0 ∧
              (∀ P ∈ S x, P.ord g = 0) ∧
              (∀ P ∈ S x', g ∈ P.toValuationSubring ∧ ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A))) := by sorry
