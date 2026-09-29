-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_nodePlaces_disjoint_smoothDiscs_of_sep
-- name    : ModularCurve.FullLevel.supersingularProlongation_nodePlaces_disjoint_smoothDiscs_of_sep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/8ac517f9-9764-5b89-8f7b-beb0391fba95
-- title:
--   Node place-sets avoid the smooth residue discs
-- statement:
--   Throughout, $q$ is a prime with $5 \le q$ and $M'$ a nonzero natural number with $q \nmid M'$; $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$ (`LiesOverPrime`), and $\kappa =$ `ResidueField A` denotes its residue field.
--
--   The level-$M'$ side consists of: a finite set $W$ of places of `modularFunctionFieldC` $\kappa\,M'$ over $\kappa$ whose members are exactly the elements of `ssPlaces` $q\,M'\,\kappa$ (hypothesis `hW`), i.e. the places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathtt{jGeomGen}\,\kappa\,M') \in \mathtt{ssJSet}\,q\,\kappa$; a distinguished element $s$ of $W$; an inclusion `hle` of `modularFunctionFieldBar` $M'$, the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field, into `fieldBar` $q\,M'$, the base change to $\overline{\mathbb{Q}}$ of the function field of the $\Gamma_H$-curve of level $q^2M'$ for $H =$ `levelH` $q\,M'$; a constant reduction $R_0$ of $A$ from `modularFunctionFieldBar` $M'$ onto `modularFunctionFieldC` $\kappa\,M'$ (a valuation subring $R_0.\mathrm{integers}$ of the source containing the image of $A$ exactly, a surjective residue map with kernel the maximal ideal, compatibility with the reduction $A \to \kappa$, the existence of scalings with nonzero residue, and a place map preserving degrees and orders); and the hypothesis $hR_0$, that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image lies in `modularFunctionFieldBar` $M'$, this image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Finally $\pi \in A$ satisfies $\pi^{q^2-1} = q$.
--
--   The smooth-point side consists of a field $F_{ss}$ over $\kappa$, a regular prolongation $R$ of $A$ from `fieldBar` $q\,M'$ onto $F_{ss}$ (a valuation subring with surjective residue map onto $F_{ss}$, kernel the maximal ideal, the prescribed behaviour on the image of $A$, and the scaling property), a finite set $N$ of places of $F_{ss}$ over $\kappa$ with $|N| = q+1$ (`hcard`), and, for every place $Q$ of $F_{ss}$ over $\kappa$, a subring $S_Q \subseteq$ `fieldBar` $q\,M'$, a ring homomorphism $\varphi_Q : A[X] \to S_Q$, a ring homomorphism $\chi_{0,Q} : S_Q \to \kappa$ and a set $D_Q$ of places of `fieldBar` $q\,M'$ over $\overline{\mathbb{Q}}$. The hypotheses on these data are: `h0`, that $F_{ss}$ contains an element transcendental over $\kappa$; `h1`, that $R$ is centred at $s$, namely that for every $f \in R_0.\mathrm{integers}$ which has non-negative order at every place of `modularFunctionFieldBar` $M'$ at which the image of the Laurent expansion `jq` of $j$ has non-negative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in `fieldBar` $q\,M'$ lies in $R.\mathrm{integers}$ and its $R$-residue is the image in $F_{ss}$ of $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$; `h2`, that $R.\mathrm{integers}$ is invariant under every level automorphism `levelAutBar` $q\,M'\,\zeta\,\gamma$ with $\zeta$ a primitive $q$-th root of unity index and $\gamma \in \Gamma_0(M')$; `hpkg`, the smooth-point chart package at each place $Q \notin N$ (fourteen clauses, summarised here: $S_Q$ contains the image of $A$; $\varphi_Q$ is formally smooth and formally unramified and sends constants to constants; $\chi_{0,Q}$ restricts to the reduction $A \to \kappa$ on constants and kills $\varphi_Q(X)$; each element of the maximal ideal of $A$ is the value at $\varphi_Q(X)$ of a unique $A$-section of $\chi_{0,Q}$ fixing constants; every $f \in S_Q$ is $R$-integral with $R$-residue in the valuation ring of $Q$ reducing to $\chi_{0,Q}(f)$; the $R$-residue of $\varphi_Q(X)$ has order $1$ at $Q$; $D_Q$ consists exactly of the rational places $P$ at which all of $S_Q$ is integral with values in $A$, the values in the maximal ideal being those of the kernel of $\chi_{0,Q}$; each $A$-section of $\chi_{0,Q}$ fixing constants is realised by a unique place of $D_Q$; the valuation rings of places of $D_Q$ are the localisations of $S_Q$ in the evident sense; a unit principle for functions of order $0$ on all of $D_Q$; and $R$-integral functions integral on all of $D_Q$ lie in $S_Q$); `hdisj`, that places $Q, Q' \notin N$ with $D_Q \cap D_{Q'} \neq \emptyset$ coincide; `hcusp`, that for $Q \notin N$ every $P \in D_Q$ has non-negative order at the image of `jq` in `fieldBar` $q\,M'$; `heqv`, that for every $\tau$ in the subgroup generated by the level automorphisms `levelAutBar` $q\,M'\,\zeta\,\gamma$ ($\gamma \in \Gamma_0(M')$) which preserves $R.\mathrm{integers}$, the induced residue automorphism `R.resAut` permutes $N$ and carries $D_Q$ to $D_{\text{resAut}\,\tau \cdot Q}$ for $Q \notin N$; and `hUniq`, that for $Q \notin N$ any quadruple $(S,\varphi,\chi_0,D)$ satisfying the same fourteen clauses has $D = D_Q$, $S = S_Q$ and the same residue character as $\chi_{0,Q}$.
--
--   The node side consists of a family of fields $F_x$ over $\kappa$ indexed by the places $x$ of $F_{ss}$ over $\kappa$, regular prolongations $R_x$ of $A$ from `fieldBar` $q\,M'$ onto $F_x$, places $b_x$ of $F_x$ over $\kappa$; an index type $\Lambda$ with subrings $C'_l \subseteq \overline{\mathbb{Q}}$ contained in $A$ (`hC'A`), each a discrete valuation domain, elements $\varpi'_l \in C'_l$, a base index $l_0$; complete discrete valuation rings $W_l$ with elements $\pi_{W,l}$, exponents $E : \Lambda \to \mathbb{N}$ and $E_0 \in \mathbb{N}$; and, for each place $nd$ of $F_{ss}$ over $\kappa$, a set $S_{nd}$ of places of `fieldBar` $q\,M'$ over $\overline{\mathbb{Q}}$, subrings $\mathcal{N}_{nd}$ and $\mathcal{N}_{nd,l}$ of `fieldBar` $q\,M'$ with $\mathcal{N}_{nd,l}$ local (`hloc`) and Noetherian (`hnoe`), and elements $c_{x}(nd), c_{y}(nd), c_{u}(nd)$ of `fieldBar` $q\,M'$.
--
--   The hypothesis `hnodes` collects the node presentations in several groups (their content is summarised here). The constant layers: the reduction $A \to \kappa$ kills exactly the multiples of $\varpi'_l$ in $C'_l$; $C'_{l_0} \subseteq C'_l$ for all $l$; $\varpi'_{l_0} \neq 0$; every element of $A$ is algebraic over $C'_{l_0}$; each $\pi_{W,l}$ is irreducible and $1 \le E_l$. The tame conditions: every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ with `tameCharacter` $A\,\pi\,\tau = 1$ fixes $\varpi'_{l_0}$, and $(\varpi'_{l_0})^{E_0} = v\,\pi^{w}$ in $A$ for some unit $v$ of $A$ and some $w \ge 1$. The node data at each $nd \in N$: rationality of $b_{nd}$, of $nd$ and of all places in $S_{nd}$; the description of $\mathcal{N}_{nd}$ as the functions integral for $R_{nd}$, for $R$ and at every place of $S_{nd}$, with values in $A$ at those places; the crossing relation $c_x(nd)\,c_y(nd) = (\varpi'_{l_0})^{E_0} c_u(nd)$ together with the residue conditions that $c_x(nd)$ has vanishing $R_{nd}$-residue and $R$-residue of order $1$ at $nd$, while $c_y(nd)$ has vanishing $R$-residue and $R_{nd}$-residue of order $1$ at $b_{nd}$; invariance of $S_{nd}$, $c_x(nd)$ and $c_y(nd)$ under the semilinear automorphism `arithmeticGalois` attached to any $\tau$ in the inertia subgroup with trivial tame character; that every element of `fieldBar` $q\,M'$ is a ratio of elements of some $\mathcal{N}_{nd,l}$, and is a $\overline{\mathbb{Q}}$-linear combination of elements of $\mathcal{N}_{nd,l_0}$ divided by one such element; and, for every $l$, the inclusions $\mathcal{N}_{nd,l_0} \subseteq \mathcal{N}_{nd,l} \subseteq \mathcal{N}_{nd}$, the characterisation of $S_{nd}$ as the set of places at which $\mathcal{N}_{nd,l}$ is integral and all its non-units take values in the maximal ideal of $A$, the containment of $C'_l$ in $\mathcal{N}_{nd,l}$, the approximation of every element of $\mathcal{N}_{nd,l}$ by a constant from $C'_l$ up to a non-unit, the transfer of $C'_l$-linear independence, membership of $c_x(nd), c_y(nd)$ in $\mathcal{N}_{nd,l}$ with $c_u(nd)$ a unit there, and an isomorphism $\iota$ of the adic completion of $\mathcal{N}_{nd,l}$ with the crossing model $\mathrm{MvPowerSeries}(\mathrm{Fin}\,2, W_l)/(X_0X_1 - \pi_{W,l}^{E_l})$, together with $\sigma : W_l \to$ the completion matching $\pi_{W,l}$ with $\varpi'_l$, realising the constants of $C'_l$ and inducing the constants `const` of the model, and two valuation dictionaries: an element of $\mathcal{N}_{nd,l}$ whose $R_{nd}$-residue is nonzero of order $n$ at $b_{nd}$ agrees with a unit multiple of $V^n$ modulo the ideal generated by `const` $\pi_{W,l}$ and $U$, and an element whose $R$-residue is nonzero of order $n$ at $nd$ agrees with a unit multiple of $U^n$ modulo the ideal generated by `const` $\pi_{W,l}$ and $V$. Further groups of `hnodes`: the sets $S_{nd}$ for distinct $nd \in N$ are disjoint; each $P \in S_{nd}$ is centred at $s$, in the sense that for $f \in R_0.\mathrm{integers}$ regular wherever the image of `jq` is and with $R_0$-residue in the valuation subring of $s$, and for $a \in A$ reducing to $s.\mathrm{evalAt}$ of that residue, the difference $P.\mathrm{evalAt}(f) - a$ lies in the maximal ideal of $A$; the level automorphisms permute $N$ compatibly with the sets $S_{nd}$ and with the rings $R_{nd}.\mathrm{integers}$, both through an explicit permutation $\tau_N$ for each $(\zeta',\gamma)$ and through `R.resAut` and `smulDisc` for each $\tau$ in the subgroup generated by the level automorphisms preserving $R.\mathrm{integers}$; the image of $R_0.\mathrm{integers}$ lies in $R_{nd}.\mathrm{integers}$ for $nd \in N$; and for each $nd \in N$ there is a ring homomorphism $j$ from `modularFunctionFieldC` $\kappa\,M'$ to $F_{nd}$ compatible with the residue maps of $R_0$ and $R_{nd}$, under which the valuation subring of $s$ is the preimage of that of $b_{nd}$.
--
--   The last hypothesis `hSEP1` is a separation requirement: for every $x \in N$ and every place $y \notin N$ of $F_{ss}$ over $\kappa$ there is $g \in$ `fieldBar` $q\,M'$ lying in $R.\mathrm{integers}$ and in $\mathcal{N}_{x,l_0}$ such that $g$ is a non-unit of $\mathcal{N}_{x,l_0}$, its $R$-residue is nonzero of order $0$ at $y$, and $g$ is integral at every rational place of `fieldBar` $q\,M'$ at which the image of `jq` has non-negative order.
--
--   Under these hypotheses the conclusion is that for every $x \in N$, every place $Q \notin N$ of $F_{ss}$ over $\kappa$ and every place $P$ of `fieldBar` $q\,M'$ over $\overline{\mathbb{Q}}$, if $P \in S_x$ then $P \notin D_Q$: the node place-set of each point of $N$ is disjoint from the residue disc of every point off $N$.
--
--   Geometrically this says that a place of the full-level function field centred at a node of the special fibre above $q$ is not centred at a smooth point of the supersingular component: the node tubes $S_x$, $x \in N$, meet none of the residue discs $D_Q$ of the smooth points. It is the disjointness clause needed when the node annuli and the smooth charts are assembled into a single cover of the component, and is used by the constructor producing node annuli, node presentations, a cover and the crossing units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_nodePlaces_disjoint_smoothDiscs_of_sep.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_nodePlaces_disjoint_smoothDiscs_of_sep
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

    (hSEP1 : (∀ x ∈ N, ∀ y : Place (ResidueField A) FSS, y ∉ N →
            ∃ (g : ↥(fieldBar q M')) (hg : g ∈ R.integers) (hg₀ : g ∈ 𝒩₀ x l₀),
              ¬ IsUnit (⟨g, hg₀⟩ : ↥(𝒩₀ x l₀)) ∧
              y.ord (R.residue ⟨g, hg⟩) = 0 ∧ R.residue ⟨g, hg⟩ ≠ 0 ∧
              ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
                0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) → g ∈ P.toValuationSubring)) :
    ∀ x ∈ N, ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P, P ∈ S x → P ∉ Dx Q := by sorry
