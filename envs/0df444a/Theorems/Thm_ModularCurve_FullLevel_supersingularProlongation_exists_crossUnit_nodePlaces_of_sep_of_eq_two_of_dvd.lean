-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_crossUnit_nodePlaces_of_sep_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_exists_crossUnit_nodePlaces_of_sep_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/d06e62e1-1db3-544e-90f3-af31ff1e1b2d
-- title:
--   Cross-units separating two nodes, case q=2
-- statement:
--   **Setting.** Fixed are a prime $q$ together with the hypothesis `hq2` that $q = 2$, a nonzero level $M'$ with $q \nmid M'$, and an auxiliary prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), i.e. $(q : \overline{\mathbb{Q}})$ is a non-unit of $A$; write $\kappa =$ `ResidueField A`. A finite set $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$ is given, and `hW` says that $W$ consists exactly of the members of `ssPlaces q M' κ`, that is, of those places $w$ which are rational (the structure map $\kappa \to w$'s residue field is surjective), satisfy `IsAffineGeomPlace`, and have `w.evalAt (jGeomGen κ M')` in `ssJSet q κ`. The hypothesis `hle` records the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'` of intermediate fields of `LaurentSeries (AlgebraicClosure ℚ)` over $\overline{\mathbb{Q}}$, the source being the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field, the target that of the function field of level $q^2M'$ with the subgroup `levelH q M'`. The datum $R_0$ is a constant reduction of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'`: a valuation subring `R₀.integers` pulling back to $A$ along the constants, a surjective residue homomorphism onto `modularFunctionFieldC κ M'` with kernel the maximal ideal, compatible with reduction of constants, with the scaling property that every nonzero element can be multiplied by a constant so as to acquire nonzero residue, and with a map on places preserving degrees and compatible with `Finsupp.mapDomain` on divisors of functions with nonzero residue. The hypothesis `hR₀` says that $R_0$ computes coefficientwise reduction: for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}$ lies in `modularFunctionFieldBar M'`, that image lies in `R₀.integers` and its $R_0$-residue, viewed as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Finally $s$ is an element of $W$ (a supersingular place), and $\pi \in \overline{\mathbb{Q}}$ satisfies $\pi^{q^2-1} = q$ and $\pi \in A$.
--
--   **Data on the Drinfeld side.** A field $F_{\mathrm{SS}}$ over $\kappa$ is given together with a regular prolongation $R$ of $A$ from `fieldBar q M'` to $F_{\mathrm{SS}}$ (a valuation subring `R.integers` pulling back to $A$ on constants, a surjective residue map onto $F_{\mathrm{SS}}$ with kernel the maximal ideal, compatible with reduction of constants, with the same scaling property), a finite set $N$ of places of $F_{\mathrm{SS}}$ over $\kappa$, and, indexed by the places $Q$ of $F_{\mathrm{SS}}$ over $\kappa$, subrings $S_Q =$ `Sx Q` of `fieldBar q M'`, ring maps $\varphi_Q : A[T] \to S_Q$, characters $\chi_{0,Q} : S_Q \to \kappa$ and sets $D_Q =$ `Dx Q` of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$. The hypotheses on these are: `h0`, that $F_{\mathrm{SS}}$ contains an element transcendental over $\kappa$; `h1`, that $R$ lies over $s$ through $R_0$, namely for $f \in$ `R₀.integers` which is regular at every place of `modularFunctionFieldBar M'` at which the image of `jq` is regular and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` lies in `R.integers` with $R$-residue the image in $F_{\mathrm{SS}}$ of `s.evalAt (R₀.residue f)`; `h2`, that `R.integers` is stable under the automorphisms `levelAutBar q M' ζ γ` for all $\zeta \in$ `Idx q` and $\gamma \in \Gamma_0(M')$; `hcard`, that $N$ has exactly $q+1$ elements; `hpkg`, a smooth-point package attached to every place $Q \notin N$ (fourteen clauses, summarised here: the constants $A$ land in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q$ and $\chi_{0,Q}$ act on constants as the inclusion and as the residue map of $A$; $\chi_{0,Q}(\varphi_Q(T)) = 0$; for each $c$ in the maximal ideal of $A$ there is a unique $A$-section of $S_Q$ lifting $\chi_{0,Q}$ with $T \mapsto c$; every element of $S_Q$ has $R$-residue in the valuation subring of $Q$, reducing to $\chi_{0,Q}$ of it; the $R$-residue of $\varphi_Q(T)$ has order $1$ at $Q$; $D_Q$ consists precisely of the rational places at which all of $S_Q$ is regular with values in $A$ and at which the values of $f \in S_Q$ are non-units exactly when $\chi_{0,Q}(f) = 0$; sections of $S_Q$ over $A$ lifting $\chi_{0,Q}$ correspond bijectively to points of $D_Q$ via evaluation; for $P \in D_Q$ the valuation subring of $P$ is the set of fractions $g/h$ with $g,h \in S_Q$ and $P$-value of $h$ nonzero; a unit principle for nonzero functions of order $0$ along all of $D_Q$; and saturation: an element of `R.integers` regular on all of $D_Q$ lies in $S_Q$); `hdisj`, that for $Q, Q' \notin N$ the sets $D_Q$ and $D_{Q'}$ are disjoint unless $Q = Q'$; `hcusp`, that for $Q \notin N$ every $P \in D_Q$ has nonnegative order on the image of `jq`; and `heqv`, that every $\tau$ in the subgroup generated by the automorphisms `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$ which preserves `R.integers` permutes $N$ through the induced automorphism `R.resAut τ` of $F_{\mathrm{SS}}$ and carries $D_Q$ to $D_{\mathrm{resAut}\,\tau \cdot Q}$ via `smulDisc` for $Q \notin N$.
--
--   **Data on the node side.** For each place $x$ of $F_{\mathrm{SS}}$ over $\kappa$ there are a field `FIx x` over $\kappa$, a regular prolongation `Rx x` of $A$ from `fieldBar q M'` onto it, and a place `bx x` of `FIx x` over $\kappa$. Further data: an index type $\Lambda$, subrings $C'_l$ of $\overline{\mathbb{Q}}$ contained in $A$ which are discrete valuation domains, elements $\varpi'_l \in C'_l$, a distinguished index $l_0$, discrete valuation domains `Wc l` complete for the maximal-ideal-adic topology with elements $\pi_{W,l}$, exponents $E : \Lambda \to \mathbb{N}$ and $E_0 \in \mathbb{N}$; sets $S(nd)$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$, subrings $\mathcal{N}(nd)$ and $\mathcal{N}_0(nd, l)$ of `fieldBar q M'` with the hypotheses `hloc` and `hnoe` that each $\mathcal{N}_0(nd,l)$ is local and Noetherian, and functions $c_x, c_y, c_u$ assigning to each place of $F_{\mathrm{SS}}$ an element of `fieldBar q M'`.
--
--   **The node hypothesis `hnodes`** (fifteen top-level conjuncts, summarised here). Six clauses concern the coefficient rings: $\varpi'_l$ generates the elements of $C'_l$ reducing to $0$ in $\kappa$; $C'_{l_0} \subseteq C'_l$ for all $l$; $\varpi'_{l_0} \neq 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_{W,l}$ is irreducible; and $1 \le E(l)$. Two further clauses are arithmetic: every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ with trivial tame character at $\pi$ fixes $\varpi'_{l_0}$; and $(\varpi'_{l_0})^{E_0} = v\,\pi^{w}$ in $A$ for some unit $v$ of $A$ and some $w \ge 1$. The main clause attaches to every $nd \in N$: rationality of `bx nd`, of $nd$ and of all $P \in S(nd)$; the description of $\mathcal{N}(nd)$ as the set of functions lying in `(Rx nd).integers`, in `R.integers` and in the valuation subring of every $P \in S(nd)$, with $A$-valued evaluations there; the crossing relation $c_x(nd)\,c_y(nd) = (\varpi'_{l_0})^{E_0} c_u(nd)$; the branch conditions that the `Rx nd`-residue of $c_x(nd)$ vanishes while the $R$-residue of $c_x(nd)$ has order $1$ at $nd$, and symmetrically that the $R$-residue of $c_y(nd)$ vanishes while the `Rx nd`-residue of $c_y(nd)$ has order $1$ at `bx nd`; invariance of $S(nd)$, $c_x(nd)$ and $c_y(nd)$ under the semilinear action `arithmeticGalois` of every inertia element with trivial tame character at $\pi$; generation of `fieldBar q M'` as the fraction field of the rings $\mathcal{N}_0(nd,l)$ and, over $l_0$, by $\overline{\mathbb{Q}}$-linear combinations of elements of $\mathcal{N}_0(nd,l_0)$ divided by a nonzero denominator there; and, for every $l$: the inclusions $\mathcal{N}_0(nd,l_0) \subseteq \mathcal{N}_0(nd,l) \subseteq \mathcal{N}(nd)$, the characterisation of $S(nd)$ as the set of places at which all of $\mathcal{N}_0(nd,l)$ is regular and at which non-units of $\mathcal{N}_0(nd,l)$ take values in the maximal ideal of $A$, the inclusion of the constants $C'_l$ into $\mathcal{N}_0(nd,l)$, the approximation of every element of $\mathcal{N}_0(nd,l)$ by a constant from $C'_l$ up to a non-unit, transfer of $C'_l$-linear independence, membership of $c_x(nd)$ and $c_y(nd)$ in $\mathcal{N}_0(nd,l)$ and unit-ness of $c_u(nd)$ there, and the existence of a ring map $\sigma$ from `Wc l` to the adic completion of $\mathcal{N}_0(nd,l)$ and a ring isomorphism $\iota$ of that completion with the crossing model `UVCrossingModel (Wc l) (πW l ^ E l)` — the quotient of the two-variable power series ring by $XY - \pi_{W,l}^{E(l)}$ — such that $\sigma(\pi_{W,l})$ is $\varpi'_l$, $\iota \circ \sigma$ is the constant embedding, every constant from $C'_l$ is in the image of $\sigma$, and the two layer conditions hold: an element whose `Rx nd`-residue is nonzero of order $n$ at `bx nd` is, modulo the ideal generated by $\pi_{W,l}$ and $U$, a unit multiple of $V^n$, and an element whose $R$-residue is nonzero of order $n$ at $nd$ is, modulo the ideal generated by $\pi_{W,l}$ and $V$, a unit multiple of $U^n$. The remaining clauses of `hnodes` state: the sets $S(nd)$, $nd \in N$, are pairwise disjoint; each $P \in S(nd)$ specialises to $s$, in the sense that for $f \in$ `R₀.integers` regular wherever `jq` is and with $R_0$-residue in the valuation subring of $s$, and for $a \in A$ reducing to `s.evalAt (R₀.residue f)`, the difference of $P$-value of $f$ and $a$ lies in the maximal ideal of $A$; for each $\zeta'$ and $\gamma \in \Gamma_0(M')$ there is a self-map $\tau_N$ of the places of $F_{\mathrm{SS}}$ preserving $N$, matching the `levelAutBar`-translate of $S(nd)$ with $S(\tau_N(nd))$ and pulling back `(Rx nd).integers` to `(Rx (τ_N nd)).integers`; every $\tau$ in the subgroup generated by the level automorphisms which preserves `R.integers` permutes $N$ via `R.resAut τ` and carries $S(nd)$ to $S(\mathrm{resAut}\,\tau \cdot nd)$ via `smulDisc`; the image of `R₀.integers` lies in `(Rx nd).integers`; and for each $nd \in N$ there is a ring homomorphism $j$ from `modularFunctionFieldC κ M'` to `FIx nd` compatible with the residues of $R_0$ and `Rx nd` and identifying the valuation subring of $s$ with the preimage of that of `bx nd`.
--
--   **The separation hypothesis `hSEP2`.** For all $x, x' \in N$ with $x \neq x'$ there exists $g \in$ `fieldBar q M'` lying in $\mathcal{N}_0(x,l_0)$ and in $\mathcal{N}_0(x',l_0)$, with $c_x(x) \in \mathcal{N}_0(x,l_0)$, such that in $\mathcal{N}_0(x,l_0)$ one has $g = c_x(x)\,u$ for some unit $u$, while $g$ is a unit of $\mathcal{N}_0(x',l_0)$.
--
--   **Conclusion.** For all $x, x' \in N$ with $x \neq x'$ there exist $g \in$ `fieldBar q M'` and a proof that $g \in$ `R.integers` such that, writing $\bar g$ for the $R$-residue of $g$: (i) $\bar g \neq 0$; (ii) the order of $\bar g$ at $x$ is nonzero; (iii) $P$-order of $g$ is $0$ for every $P \in S(x)$; and (iv) for every $P \in S(x')$, $g$ lies in the valuation subring of $P$ and its $P$-value lies in $A$ and is a unit of $A$.
--
--   This is the cross-unit step for the supersingular (Drinfeld) component of the full-level modular curve in the case $q = 2$, under the rigid-level guard provided by an auxiliary prime $\ell \equiv 11 \pmod{12}$ dividing $M'$: starting from a function that is a unit times the crossing parameter $c_x$ in the semilocal ring at one node and a unit at another, it produces a global function on the component whose reduction is nonzero with nonzero order at the first node, has order zero along the node tube of the first node, and is a unit along the node tube of the second. It feeds the subsequent construction of node annuli and the zero-free covering of the component, [`ModularCurve.FullLevel.supersingularProlongation_exists_nodeAnnuli_nodePresentations_cover_crossUnits_zeroFree_of_nodePresentations_nodeCharts_hasseJ_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.supersingularProlongation_exists_nodeAnnuli_nodePresentations_cover_crossUnits_zeroFree_of_nodePresentations_nodeCharts_hasseJ_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_exists_crossUnit_nodePlaces_of_sep_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_exists_crossUnit_nodePlaces_of_sep_of_eq_two_of_dvd
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
