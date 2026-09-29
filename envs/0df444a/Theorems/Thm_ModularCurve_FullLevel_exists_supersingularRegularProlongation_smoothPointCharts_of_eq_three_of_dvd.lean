-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/f0020fff-6d0f-5240-8ae0-e34d48ab6008
-- title:
--   Supersingular regular prolongation with smooth-point charts, q=3
-- statement:
--   Fix a prime $q$ with $q=3$, a nonzero natural number $M'$ with $q\nmid M'$, and a prime $\ell$ with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, write $\kappa=\mathrm{ResidueField}\,A$, and let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places, i.e. the rational affine geometric places at which the geometric $j$-generator evaluates into the supersingular $j$-set in characteristic $q$. Assume $\mathrm{modularFunctionFieldBar}\,M'$, the $\overline{\mathbb Q}$-base change of the full level-$M'$ modular function field inside $\overline{\mathbb Q}$-Laurent series, is contained in $\mathrm{fieldBar}\,q\,M'$, the corresponding base-changed $x_H$-function field of level $q^2M'$ for $H$ the kernel of $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$. Let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ (a valuation subring restricting to $A$ on constants, with surjective residue map whose kernel is the maximal ideal, compatible with reduction of $A$, a scaling property for nonzero elements, and a degree- and divisor-compatible map on places), assumed to reduce coefficientwise: every Laurent series $y$ over $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0$'s integers, with residue the coefficientwise reduction of $y$. Finally let $s\in W$. Then there are a field $\mathrm{FSS}$ over $\kappa$ and a regular prolongation $R$ of $A$ to $\mathrm{fieldBar}\,q\,M'$ with residue field $\mathrm{FSS}$ (a valuation subring restricting to $A$ on $\overline{\mathbb Q}$, surjective residue map with kernel the maximal ideal, compatible with reduction of $A$, and the scaling property) such that: (i) $\mathrm{FSS}$ contains an element transcendental over $\kappa$; (ii) for every $f$ in the integers of $R_0$ which has nonnegative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ where the element $\mathrm{coeffEmb}\,\overline{\mathbb Q}\,jq$ has nonnegative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in the integers of $R$ and its $R$-residue is the image in $\mathrm{FSS}$ of the value of the $R_0$-residue of $f$ at $s$; (iii) for every $\zeta\in\mathrm{Idx}\,q$ (a primitive $q$-th root of unity in $\overline{\mathbb Q}$) and every $\gamma\in\Gamma_0(M')\subseteq SL(2,\mathbb Z)$, the integers of $R$ are preserved by pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; and (iv) there exist a finite set $N$ of places of $\mathrm{FSS}$ over $\kappa$ with $|N|=q+1$ and, for each place $Q$ of $\mathrm{FSS}$ over $\kappa$, a subring $S_Q$ of $\mathrm{fieldBar}\,q\,M'$, ring maps $\varphi_Q\colon A[X]\to S_Q$ and $\chi_{0,Q}\colon S_Q\to\kappa$, and a set $D_Q$ of places of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$, such that for all $Q\notin N$: $S_Q$ contains the image of $A$; $\varphi_Q$ is formally smooth and formally unramified, sends constants $a\in A$ to the image of $a$, and satisfies $\chi_{0,Q}(\varphi_Q(C\,a))=$ the reduction of $a$ and $\chi_{0,Q}(\varphi_Q(X))=0$; for each $c\in A$ with zero reduction there is exactly one ring map $\chi\colon S_Q\to A$ fixing constants, reducing to $\chi_{0,Q}$ and sending $\varphi_Q(X)$ to $c$; each $f\in S_Q$ lies in the integers of $R$ with $R$-residue in the valuation subring of $Q$, whose reduction in the residue field of $Q$ is the image of $\chi_{0,Q}(f)$; the $R$-residue of $\varphi_Q(X)$ has order $1$ at $Q$; $D_Q$ consists exactly of the rational places $P$ such that every $f\in S_Q$ lies in the valuation subring of $P$ with $P$-value in $A$, and the $A$-valuation of that value is $<1$ precisely when $\chi_{0,Q}(f)=0$; every $\chi$ as above fixing constants and reducing to $\chi_{0,Q}$ arises from a unique $P\in D_Q$ via $P$-evaluation; for $P\in D_Q$ the valuation subring of $P$ is the set of fractions $g/h$ with $g,h\in S_Q$ and $P$-value of $h$ nonzero; any nonzero $f$ of order $0$ at all $P\in D_Q$ becomes a unit of $S_Q$ after multiplication by a nonzero constant of $\overline{\mathbb Q}$; and any $f$ in the integers of $R$ lying in all valuation subrings of $D_Q$ lies in $S_Q$. Moreover the sets $D_Q$ for distinct $Q,Q'\notin N$ are disjoint; for $Q\notin N$ the element $\mathrm{coeffEmb}\,\overline{\mathbb Q}\,jq$ has nonnegative order at every $P\in D_Q$; and for every $\tau$ in the subgroup generated by the automorphisms $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma\in\Gamma_0(M')$ which preserves the integers of $R$, the induced residue automorphism of $\mathrm{FSS}$ leaves $N$ invariant and carries $D_Q$ to $D_{\tau\cdot Q}$ for $Q\notin N$, in the sense that $\{P:\tau^{-1}\cdot P\in D_Q\}=D_{\tau\cdot Q}$.
--
--   This provides, in residue characteristic $3$, the local arithmetic data at a supersingular point of the level-$M'$ curve for the component of the full level-$q$ modular curve cut out by $H$: a regular prolongation of the valuation ring $A$ to the geometric function field, its $q+1$ distinguished residue places, and étale coordinate charts with their residue discs at the remaining points, all equivariant for the level automorphisms over $\Gamma_0(M')$. It is the $q=3$ companion of the corresponding statements for $q=2$ and $q\ge 5$, the auxiliary prime $\ell\equiv 11\pmod{12}$ dividing $M'$ serving to rigidify the supersingular point where extra automorphisms occur in characteristic $3$; it is used by [`ModularCurve.FullLevel.exists_supersingularChart_local_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularChart_local_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_of_eq_three_of_dvd
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
    (s : ↥W) :
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
            (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q))) := by sorry
