-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree
-- name    : ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/730fa6da-2bf3-5e55-995f-2d1fad96cdb4
-- title:
--   Semilinear transport of smooth-point packages off the ends
-- statement:
--   The setting is the following. Let $q$ be a prime with $5 \le q$, let $M'$ be a non-zero natural number with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime q`, i.e. $q$ lies in the non-units of $A$; write $\kappa =$ `ResidueField A`. Let $W$ be a finite set of places of `modularFunctionFieldC κ M'` over $\kappa$, characterised by `hW` as consisting exactly of the members of `ssPlaces q M' κ`: the places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}$ of `jGeomGen κ M'` $\in$ `ssJSet q κ`. The inclusion `hle` records that `modularFunctionFieldBar M'`, the $\overline{\mathbb{Q}}$-base change inside $\overline{\mathbb{Q}}((q))$ of the full level-$M'$ modular function field, is contained in `fieldBar q M'`, the corresponding base change of the function field of $X_H(q^2M')$ for the subgroup `levelH q M'` of $(\mathbb{Z}/q^2M')^\times$. Further data: a constant reduction $R_0$ of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` (a valuation subring `R₀.integers`, a surjective residue homomorphism onto the reduced field with kernel the maximal ideal, a map on places, and the usual compatibilities), subject to `hR₀`: every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}((q))$ lies in `modularFunctionFieldBar M'` lies in `R₀.integers`, and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$; and a chosen element $s \in W$, i.e. a supersingular place.
--
--   On top of this: a field $F_{ss}$ which is a $\kappa$-algebra, a regular prolongation $R$ of $A$ from `fieldBar q M'` to $F_{ss}$ (valuation subring `R.integers`, surjective residue map with kernel the maximal ideal, compatible with $A$ and with its residue field), a finite set $N$ of places of $F_{ss}$ over $\kappa$, and, for each place $Q$ of $F_{ss}$ over $\kappa$, a subring $S_Q \subseteq$ `fieldBar q M'` (`Sx Q`), a ring homomorphism $\varphi_Q : A[T] \to S_Q$ (`φx Q`), a ring homomorphism $\chi_{0,Q} : S_Q \to \kappa$ (`χ₀x Q`), and a set $D_Q$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$ (`Dx Q`). Write $j$ for the element of `modularFunctionFieldBar M'` given by the coefficientwise image `coeffEmb (AlgebraicClosure ℚ) jq` of the $q$-expansion of the modular invariant, and also for its image in `fieldBar q M'` under `hle`.
--
--   The hypotheses on these data are: `h0`, that $F_{ss}$ contains an element transcendental over $\kappa$; `h1`, that $R$ lies over $s$, in the sense that for every $f \in$ `R₀.integers` which is regular wherever $j$ is (for every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$, $0 \le P.\mathrm{ord}(j)$ implies $0 \le P.\mathrm{ord}(f)$) and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` lies in `R.integers` and its $R$-residue is the image in $F_{ss}$ of $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$; `h2`, that for every $\zeta$ in `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ with $\gamma \in \Gamma_0(M')$, the preimage of `R.integers` under `levelAutBar q M' ζ γ` is `R.integers`; and `hcard`, that $N$ has exactly $q+1$ elements.
--
--   The hypothesis `hpkg` asserts that for every place $Q \notin N$ the quadruple $(S_Q, \varphi_Q, \chi_{0,Q}, D_Q)$ is a smooth-point package, namely (i) $S_Q$ contains the image of $A$; (ii) and (iii) $\varphi_Q$ is formally smooth and formally unramified; (iv) $\varphi_Q(C\,a)$ is the image of $a$ in `fieldBar q M'` for all $a \in A$; (v) $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$; (vi) $\chi_{0,Q}(\varphi_Q(X)) = 0$; (vii) for every $c \in A$ with residue $0$ there is a unique ring homomorphism $\chi : S_Q \to A$ with $\chi(\varphi_Q(C\,a)) = a$ for all $a \in A$, with residue of $\chi(f)$ equal to $\chi_{0,Q}(f)$ for all $f \in S_Q$, and with $\chi(\varphi_Q(X)) = c$; (viii) every $f \in S_Q$ lies in `R.integers`, its $R$-residue lies in the valuation subring of $Q$, and the residue there of that $R$-residue is the image of $\chi_{0,Q}(f)$ in the residue field of $Q$; (ix) $\varphi_Q(X)$ lies in `R.integers` and $Q.\mathrm{ord}$ of its $R$-residue equals $1$; (x) a place $P$ belongs to $D_Q$ exactly when $P$ is rational (the map $\overline{\mathbb{Q}} \to P.\mathrm{ResidueField}$ is surjective), every $f \in S_Q$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f) \in A$, and for every $f \in S_Q$ one has $A$-valuation of $P.\mathrm{evalAt}(f)$ less than $1$ if and only if $\chi_{0,Q}(f) = 0$; (xi) for every ring homomorphism $\chi : S_Q \to A$ fixing the image of $A$ and lifting $\chi_{0,Q}$ there is a unique $P \in D_Q$ with $P.\mathrm{evalAt}(f) = \chi(f)$ for all $f \in S_Q$; (xii) for $P \in D_Q$, an element $f$ lies in the valuation subring of $P$ if and only if there are $g, h \in S_Q$ with $P.\mathrm{evalAt}(h) \ne 0$ and $f h = g$; (xiii) every $f \ne 0$ with $P.\mathrm{ord}(f) = 0$ for all $P \in D_Q$ becomes, after multiplication by the image of some non-zero $c \in \overline{\mathbb{Q}}$, a unit of $S_Q$; and (xiv) every $f \in$ `R.integers` lying in the valuation subring of every $P \in D_Q$ lies in $S_Q$.
--
--   Three further hypotheses constrain these packages: `hdisj`, that for $Q, Q' \notin N$ the discs $D_Q$ and $D_{Q'}$ are disjoint unless $Q = Q'$; `hcusp`, that for $Q \notin N$ and $P \in D_Q$ one has $0 \le P.\mathrm{ord}(j)$, i.e. the discs avoid the poles of $j$; and `heqv`, that for every $\tau$ in the subgroup of $\mathrm{Aut}_{\overline{\mathbb{Q}}}($`fieldBar q M'`$)$ generated by the automorphisms `levelAutBar q M' ζ γ` with $\zeta$ in `Idx q` and $\gamma \in \Gamma_0(M')$, and every proof that $\tau$ preserves `R.integers`, the induced residual automorphism `R.resAut` permutes $N$ (for all $Q$, $\mathrm{resAut}(\tau)\cdot Q \in N$ if and only if $Q \in N$) and carries discs to discs: for $Q \notin N$, `smulDisc τ (Dx Q)` $= D_{\mathrm{resAut}(\tau)\cdot Q}$.
--
--   Finally, two hypotheses pin the packages down. `hNpkg` states that no place $Q \in N$ admits a cusp-free smooth-point package: for all $Q \in N$ and all data $(S, \varphi, \chi_0, D)$ of the above shape, the conjunction of the fourteen clauses (i)–(xiv), stated for $(S, \varphi, \chi_0, D)$ and $Q$, together with the clause that $0 \le P.\mathrm{ord}(j)$ for all $P \in D$, is false. `hUniq` states the uniqueness off $N$: for $Q \notin N$, any data $(S, \varphi, \chi_0, D)$ satisfying the fourteen clauses (i)–(xiv) for $Q$ satisfies $D = D_Q$ and $S = S_Q$ as sets, and $\chi_0$ agrees with $\chi_{0,Q}$ on $S$.
--
--   Under these hypotheses the conclusion is as follows. Let $g$ be a semilinear automorphism of `fieldBar q M'` over $\overline{\mathbb{Q}}$, that is, a pair consisting of a ring automorphism of the field and a ring automorphism `SemilinearAut.baseAut g` of $\overline{\mathbb{Q}}$ intertwined by the structure map, and assume: `hgA`, that `baseAut g` preserves $A$ ($x \in A$ if and only if `baseAut g x` $\in A$); `hgR`, that $g \cdot f \in$ `R.integers` if and only if $f \in$ `R.integers`; and `hgj`, that $g$ fixes $j$. Let $\psi$ be a ring automorphism of $\kappa$ with `hψ`: $\psi$ of the residue of $a$ equals the residue of `baseAut g a` for every $a \in A$. Let $\phi$ be a ring automorphism of $F_{ss}$ with `hφ`: for every $f \in$ `R.integers`, the $R$-residue of $g \cdot f$ equals $\phi$ of the $R$-residue of $f$. Then for all places $Q, Q'$ of $F_{ss}$ over $\kappa$ such that $Q \notin N$ and $Q'$ is the transport of $Q$ along $\phi$ (for all $y \in F_{ss}$, $y$ lies in the valuation subring of $Q'$ if and only if $\phi^{-1}(y)$ lies in that of $Q$), the following hold: first, $Q' \notin N$; secondly, $f \in S_Q$ if and only if $g \cdot f \in S_{Q'}$, for every $f \in$ `fieldBar q M'`; thirdly, for every $f \in S_Q$ one has $\chi_{0,Q'}(g \cdot f) = \psi(\chi_{0,Q}(f))$; and fourthly, for every place $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$, $P \in D_Q$ if and only if $g \cdot P \in D_{Q'}$.
--
--   This is the equivariance statement for the chart data attached to the supersingular component in the stable reduction of $X_H(q^2M')$ at $q$: a semilinear automorphism preserving the valuation ring $A$, the prolongation $R$ and the modular invariant $j$ transports the local ring, the residue character and the residue disc at a place $Q$ off the set $N$ of $q+1$ ends to those at the transported place, which again lies off $N$. It is used in the assembly of the supersingular chart package [`ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ`](thm.html#ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ), where the transport supplies the Galois- and level-equivariance of the charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree
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

    (hNpkg : (∀ Q ∈ N, ∀ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
          (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          ¬ (
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
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) ∧

          (∀ P ∈ D, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))))))

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
          (∀ (f : ↥(fieldBar q M')) (hf : f ∈ S) (hf' : f ∈ Sx Q), χ₀ ⟨f, hf⟩ = χ₀x Q ⟨f, hf'⟩))) :
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
              (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ Dx Q ↔ g • P ∈ Dx Q')) := by sorry
