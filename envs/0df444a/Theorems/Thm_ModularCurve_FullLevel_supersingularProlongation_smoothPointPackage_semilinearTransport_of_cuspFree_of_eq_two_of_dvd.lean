-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/206e77f1-faf8-5d25-8a45-686a92b35587
-- title:
--   Semilinear transport of supersingular smooth-point packages (q=2)
-- statement:
--   Throughout, $q$ is a prime with $q = 2$, $M'$ is a nonzero natural number not divisible by $q$, and $\ell$ is a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a nonunit of $A$; $\kappa =$ `ResidueField A` denotes its residue field. The finite set $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$ is required by `hW` to consist exactly of the members of `ssPlaces q M' κ`, that is of those places $w$ which are rational, satisfy the predicate `IsAffineGeomPlace`, and have $w$-value of `jGeomGen κ M'` in `ssJSet q κ`; and $s$ is an element of $W$. The inclusion `hle` asserts $\overline{\mathbb{Q}}\cdot F(M') \le F_{\mathrm{bar}}$, where $\overline{\mathbb{Q}}\cdot F(M') =$ `modularFunctionFieldBar M'` is the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field inside $\overline{\mathbb{Q}}((q))$, and $F_{\mathrm{bar}} =$ `fieldBar q M'` is the corresponding base change of the function field of level $H =$ `levelH q M'` inside level $q^2M'$, $H$ being the kernel of the reduction map on unit groups. Finally $R_0$ is a `ConstantReduction` of $A$ from $\overline{\mathbb{Q}}\cdot F(M')$ to `modularFunctionFieldC κ M'`, and the hypothesis `hR₀` requires that for every Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbb{Q}}((q))$ lies in $\overline{\mathbb{Q}}\cdot F(M')$, that element belongs to `R₀.integers` and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$.
--
--   The data to be transported consist of: a field $F_{ss}$ which is an algebra over $\kappa$; a `RegularProlongation` $R$ of $A$ from $F_{\mathrm{bar}}$ to $F_{ss}$ (a valuation subring `R.integers` of $F_{\mathrm{bar}}$ whose intersection with $\overline{\mathbb{Q}}$ is $A$, together with a surjective residue map onto $F_{ss}$ with kernel the maximal ideal, compatible with $A \to \kappa$, and such that every nonzero element of $F_{\mathrm{bar}}$ has a nonzero residue after scaling by a constant); a finite set $N$ of places of $F_{ss}$ over $\kappa$; and, indexed by places $Q$ of $F_{ss}$ over $\kappa$, a subring $S_Q =$ `Sx Q` of $F_{\mathrm{bar}}$, a ring homomorphism $\varphi_Q : A[X] \to S_Q$, a ring homomorphism $\chi_{0,Q} : S_Q \to \kappa$, and a set $D_Q =$ `Dx Q` of places of $F_{\mathrm{bar}}$ over $\overline{\mathbb{Q}}$.
--
--   The hypotheses on these data are: `h0`, that $F_{ss}$ contains an element transcendental over $\kappa$; `h1`, which pins $R$ over the place $s$, namely for every $f$ in `R₀.integers` such that $f$ has nonnegative order at every place of $\overline{\mathbb{Q}}\cdot F(M')$ at which the element $j$ (the image of the $q$-expansion `jq` under `coeffEmb`) has nonnegative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $F_{\mathrm{bar}}$ lies in `R.integers` and its $R$-residue is the image under $\kappa \to F_{ss}$ of the value of the $R_0$-residue of $f$ at $s$; `h2`, that `R.integers` is invariant under each level automorphism `levelAutBar q M' ζ γ` for $\zeta \in$ `Idx q` and $\gamma \in \Gamma_0(M')$; and `hcard`, that $N$ has exactly $q+1$ elements.
--
--   The hypothesis `hpkg` requires, for every place $Q \notin N$, that the quadruple $(S_Q, \varphi_Q, \chi_{0,Q}, D_Q)$ be a smooth-point package, in the following fourteen clauses: the image of $A$ in $F_{\mathrm{bar}}$ lies in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C\,a)$ is the image of $a$ in $F_{\mathrm{bar}}$ for $a \in A$; $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$; $\chi_{0,Q}(\varphi_Q(X)) = 0$; for every $c \in A$ with residue $0$ there is a unique ring homomorphism $\chi : S_Q \to A$ splitting $a \mapsto \varphi_Q(C\,a)$, reducing to $\chi_{0,Q}$, and sending $\varphi_Q(X)$ to $c$; every $f \in S_Q$ lies in `R.integers`, its $R$-residue lies in the valuation subring of $Q$, and the residue there agrees with the image of $\chi_{0,Q}(f)$ under $\kappa \to Q.\mathrm{ResidueField}$; the $R$-residue of $\varphi_Q(X)$ has $Q$-order $1$; $D_Q$ consists exactly of the rational places $P$ of $F_{\mathrm{bar}}$ over $\overline{\mathbb{Q}}$ at which every $f \in S_Q$ is regular with value in $A$, and for which $|P(f)|<1$ in the valuation of $A$ holds precisely when $\chi_{0,Q}(f)=0$; every section $\chi : S_Q \to A$ over $A$ reducing to $\chi_{0,Q}$ is realised by a unique $P \in D_Q$ with $P(f) = \chi(f)$ for all $f \in S_Q$; for $P \in D_Q$, an element $f$ of $F_{\mathrm{bar}}$ lies in the valuation subring of $P$ exactly when $f = g/h$ with $g,h \in S_Q$ and $P(h) \neq 0$; a unit principle, that a nonzero $f$ of order $0$ at all $P \in D_Q$ becomes a unit of $S_Q$ after multiplication by a nonzero constant from $\overline{\mathbb{Q}}$; and that an element of `R.integers` regular at all $P \in D_Q$ belongs to $S_Q$.
--
--   The remaining hypotheses on the family are: `hdisj`, that for $Q, Q' \notin N$ the discs $D_Q$ and $D_{Q'}$ are disjoint unless $Q = Q'$; `hcusp`, the cusp-free condition that for $Q \notin N$ every $P \in D_Q$ has nonnegative order at the image of $j$ in $F_{\mathrm{bar}}$; `heqv`, that for every $\tau$ in the subgroup of $\overline{\mathbb{Q}}$-automorphisms of $F_{\mathrm{bar}}$ generated by the automorphisms `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$, and every proof that $\tau$ preserves `R.integers`, the induced automorphism `R.resAut τ` of $F_{ss}$ acts on places so as to preserve $N$, and for $Q \notin N$ carries $D_Q$ to $D_{\,\mathrm{resAut}\,\tau \cdot Q}$ in the sense of `smulDisc`; `hNpkg`, that no place $Q \in N$ admits any quadruple $(S, \varphi, \chi_0, D)$ satisfying the fourteen package clauses above together with the cusp-free clause for $D$; and `hUniq`, that for $Q \notin N$ any quadruple $(S, \varphi, \chi_0, D)$ satisfying the fourteen package clauses coincides with $(S_Q, \varphi_Q, \chi_{0,Q}, D_Q)$, in that $D = D_Q$ as sets of places, $S = S_Q$ as subsets of $F_{\mathrm{bar}}$, and $\chi_0$ and $\chi_{0,Q}$ agree on common elements.
--
--   The conclusion is a transport statement. Let $g$ be a semilinear automorphism of $F_{\mathrm{bar}}$ over $\overline{\mathbb{Q}}$, i.e. a pair consisting of a ring automorphism of $F_{\mathrm{bar}}$ and a ring automorphism `SemilinearAut.baseAut g` of $\overline{\mathbb{Q}}$ intertwined by the structure map, subject to: `hgA`, that `baseAut g` preserves $A$ in both directions; `hgR`, that $g$ preserves `R.integers`; and `hgj`, that $g$ fixes the image of $j$ in $F_{\mathrm{bar}}$. Let $\psi$ be a ring automorphism of $\kappa$ with `hψ`: $\psi$ of the residue of $a \in A$ is the residue of `baseAut g` applied to $a$; and let $\phi$ be a ring automorphism of $F_{ss}$ with `hφ`: $R$-residue of $g \cdot f$ equals $\phi$ of the $R$-residue of $f$, for all $f \in$ `R.integers`. Then for all places $Q, Q'$ of $F_{ss}$ over $\kappa$ with $Q \notin N$ and such that $y$ lies in the valuation subring of $Q'$ exactly when $\phi^{-1}(y)$ lies in that of $Q$, the following hold: $Q' \notin N$; the subrings correspond, $f \in S_Q \iff g \cdot f \in S_{Q'}$ for all $f \in F_{\mathrm{bar}}$; the residue characters correspond, $\chi_{0,Q'}(g \cdot f) = \psi(\chi_{0,Q}(f))$ for all $f \in S_Q$; and the residue discs correspond, $P \in D_Q \iff g \cdot P \in D_{Q'}$ for every place $P$ of $F_{\mathrm{bar}}$ over $\overline{\mathbb{Q}}$.
--
--   This is the functoriality (Galois-semilinear equivariance) step for the smooth-point charts on the supersingular component of the stable reduction of the full level-$q^2M'$ modular curve, in the case $q = 2$ with an auxiliary rigidifying prime $\ell \equiv 11 \pmod{12}$ dividing $M'$: a semilinear automorphism of the function field that preserves $A$, the prolongation $R$ and the function $j$ transports the chart data attached to a place $Q$ outside the $q+1$ distinguished ends to the data attached to the image place $Q'$. It is used in the assembly of the supersingular regular prolongation together with its smooth-point charts, node presentations, crossing units and inertia data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree_of_eq_two_of_dvd
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
