-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaSmoothPointCharts_of_igusaGaussRing_allInertia
-- name    : ModularCurve.FullLevel.exists_igusaSmoothPointCharts_of_igusaGaussRing_allInertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/7baaf2b5-0532-5dfe-8ff6-a9a4a7e7b5cd
-- title:
--   Smooth-point charts for the Igusa Gauss ring at ∞
-- statement:
--   Throughout, $\overline{\mathbb Q}$ denotes `AlgebraicClosure ℚ`. The data are: a prime $q$ with $5\le q$ (`hq`); a non-zero natural number $M'$ with $q\nmid M'$ (`hqM'`); a valuation subring $A$ of $\overline{\mathbb Q}$ satisfying `A.LiesOverPrime q`, that is, $q$ is a non-unit of $A$ (`hA`); and, writing $\kappa$ for the residue field of $A$, the following fields of Laurent series: `modularFunctionFieldC κ M'`, the subfield of $\kappa((Q))$ generated over $\kappa$ by the two series `jqModC κ` and `jqNModC κ M'`; `modularFunctionFieldBar M'`, the subfield of $\overline{\mathbb Q}((Q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of `modularFunctionFieldFull M'` (itself generated over $\mathbb Q$ by the divisor expansions of level $M'$); and `fieldBar q M'`, which is `xHFunctionFieldBar (q^2*M') (levelH q M')`, the analogous base change to $\overline{\mathbb Q}$ of the $q$-expansion function field of $\Gamma_H(q^2M')$, where `levelH q M'` is the kernel of the unit-group reduction map `ZMod.unitsMap` attached to the divisibility `dvd_sq_mul q M'`. A place `Place K F` is a valuation subring of $F$ containing the image of $K$, distinct from $F$ and a principal ideal ring; `ord`, `IsRational` (surjectivity of $K\to$ residue field) and `evalAt` (value in $K$ at a place, $0$ outside the valuation subring) are as defined for places.
--
--   The hypotheses fall into the following groups.
--
--   Supersingular locus. $W$ is a finite set of places of `modularFunctionFieldC κ M'` over $\kappa$, and `hW` states that a place belongs to $W$ precisely when it lies in `ssPlaces q M' κ`, i.e. it is rational, is an affine geometric place, and its value at `jGeomGen κ M'` lies in `ssJSet q κ`.
--
--   Reduction of the level-$M'$ field. `hle` asserts the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'`. $R_0$ is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'`: a valuation subring `R₀.integers` lying over $A$ (an element of $\overline{\mathbb Q}$ is in $A$ exactly when its image is in `R₀.integers`), together with a surjective residue homomorphism onto `modularFunctionFieldC κ M'` whose kernel is the maximal ideal and which is compatible with $A\to\kappa$ on constants, a scaling property making every non-zero element into one with non-zero residue, and a map on places preserving degrees and compatible with divisors of functions. `hR₀` is the coefficientwise compatibility: for every Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbb Q}((Q))$ lies in `modularFunctionFieldBar M'`, that element lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$.
--
--   Igusa family. $\zeta$ is a primitive $q$-th root of unity in $\overline{\mathbb Q}$ (an element of `Idx q`), and `OIg` assigns a valuation subring of `fieldBar q M'` to each point of $\mathbb P^1(\mathbb F_q)$ ([`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21)). `hIg_inf` describes the ring at `lineInfty q` $=[1:0]$ as a Gauss ring: $f$ lies in it exactly when there are Laurent series $x,y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ to $\kappa$ is non-zero and $f\cdot y=x$ as Laurent series over $\overline{\mathbb Q}$. `hIg` asserts that each $\ell$ is reached from $[1:0]$ by the mod-$q$ reduction `redQ q γ` of some $\gamma\in\Gamma_0(M')$, with `OIg ℓ` the preimage of `OIg (lineInfty q)` under `levelAutBar q M' ζ γ`; `hIg_inj` that `OIg` is injective; `hIg_perm` that for every $\zeta'$ and every $\gamma\in\Gamma_0(M')$ the preimage operation along `levelAutBar q M' ζ' γ` permutes the family `OIg`.
--
--   Supersingular (Drinfeld) family. `OSS` assigns a valuation subring of `fieldBar q M'` to each $s\in W$. `hSS_A` says each `OSS s` lies over $A$. `hSS_over` concerns $s\in W$ and $f\in$ `R₀.integers` subject to the integrality condition that $\operatorname{ord}_P f\ge 0$ at every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the element $j$ — the coefficient embedding of `jq` — has non-negative order; if moreover the $R_0$-residue of $f$ lies in the valuation subring of $s$, then the image of $f$ in `fieldBar q M'` lies in `OSS s`, and for every $a\in A$ whose residue equals the value of $s$ at that $R_0$-residue, the difference of the image of $f$ and the image of $a$ lies in `OSS s` and in its maximal ideal. `hSS_fix` says each `OSS s` is its own preimage under every `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$. `hSS_tr` provides, for each $s\in W$, an element $t\in$ `OSS s` such that $t-a$ is a unit of `OSS s` for every $a\in A$.
--
--   The prolongation. $R$ is a `RegularProlongation` of $A$ from `fieldBar q M'` to `xHFunctionFieldC κ (q^2*M') (levelH q M')`: a valuation subring `R.integers` lying over $A$ with a surjective residue homomorphism whose kernel is its maximal ideal, compatible with $A\to\kappa$ on constants and satisfying the scaling property. `hR` identifies `R.integers` with `OIg (lineInfty q)`, and `hR₀O` says that $f$ lies in `R₀.integers` exactly when its image in `fieldBar q M'` lies in `OIg (lineInfty q)`. Finally $\pi\in\overline{\mathbb Q}$ satisfies $\pi^{q^2-1}=q$ (`hπ`) and $\pi\in A$ (`hπP`).
--
--   Conclusion. There exist a finite set `NIg` of places of `xHFunctionFieldC κ (q^2*M') (levelH q M')` over $\kappa$ and, for every place $Q$ of that field, a subring $S_Q$ of `fieldBar q M'`, a ring homomorphism $\varphi_Q:A[X]\to S_Q$, a ring homomorphism $\chi_Q:S_Q\to\kappa$ and a set $D_Q$ of places of `fieldBar q M'` over $\overline{\mathbb Q}$, such that the cardinality of `NIg` equals that of $W$, and the following hold.
--
--   First, for every $Q\notin$ `NIg`: (a) the image of every $a\in A$ lies in $S_Q$; (b) $\varphi_Q$ is formally smooth and formally unramified; (c) $\varphi_Q(C\,a)$ is the image of $a$ in `fieldBar q M'`, for all $a\in A$; (d) $\chi_Q(\varphi_Q(C\,a))$ is the residue of $a$, for all $a\in A$; (e) $\chi_Q(\varphi_Q(X))=0$; (f) for every $c\in A$ with residue $0$ there is exactly one ring homomorphism $\chi:S_Q\to A$ with $\chi(\varphi_Q(C\,a))=a$ for all $a\in A$, with residue of $\chi(f)$ equal to $\chi_Q(f)$ for all $f\in S_Q$, and with $\chi(\varphi_Q(X))=c$; (g) every $f\in S_Q$ lies in `R.integers`, its $R$-residue lies in the valuation subring of $Q$, and the residue there equals the image of $\chi_Q(f)$ under $\kappa\to Q.\mathrm{ResidueField}$; (h) $\varphi_Q(X)$ lies in `R.integers` and its $R$-residue has order $1$ at $Q$; (i) $D_Q$ consists exactly of the places $P$ that are rational, for which every $f\in S_Q$ lies in the valuation subring of $P$ with $P$-value in $A$, and for which, for every $f\in S_Q$, the $A$-valuation of the $P$-value of $f$ is $<1$ precisely when $\chi_Q(f)=0$; (j) every ring homomorphism $\chi:S_Q\to A$ which is the identity on $\varphi_Q(C\,a)$, $a\in A$, and lifts $\chi_Q$ is realised by exactly one place $P\in D_Q$, in the sense that $P$-values on $S_Q$ are the values of $\chi$; (k) for $P\in D_Q$ the valuation subring of $P$ is the set of quotients $g/h$ with $g,h\in S_Q$ and $P$-value of $h$ non-zero; (l) every non-zero $f$ of order $0$ at all $P\in D_Q$ becomes a unit of $S_Q$ after multiplication by some non-zero constant from $\overline{\mathbb Q}$; (m) every $f\in$ `R.integers` lying in the valuation subring of every $P\in D_Q$ lies in $S_Q$.
--
--   Second, the discs separate the non-nodal places: for $Q,Q'\notin$ `NIg`, if some $P$ lies in both $D_Q$ and $D_{Q'}$ then $Q=Q'$.
--
--   Third, inertia equivariance: for every $\tau$ in `A.inertiaSubgroupIn ℚ` (the image in the automorphism group of $\overline{\mathbb Q}$ over $\mathbb Q$ of the inertia subgroup of $A$) and every $Q\notin$ `NIg`, the subring $S_Q$ is stable under the coefficientwise action [`ModularCurve.arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54) — membership in $S_Q$ holds for $f$ exactly when it holds for $\tau\cdot f$ — and $\chi_Q$ is invariant under that action.
--
--   Fourth, the nodes come from the supersingular places: there is a ring homomorphism $j$ from `modularFunctionFieldC κ M'` to `xHFunctionFieldC κ (q^2*M') (levelH q M')` such that for every $f\in$ `R₀.integers` the image of $f$ in `fieldBar q M'` lies in `R.integers` with $R$-residue $j$ applied to the $R_0$-residue of $f$, and such that $Q\in$ `NIg` precisely when there is $s\in W$ with the valuation subring of $s$ the preimage under $j$ of the valuation subring of $Q$.
--
--   Fifth and sixth, equivariance under the level automorphisms: let $G$ be the subgroup of $\overline{\mathbb Q}$-algebra automorphisms of `fieldBar q M'` generated by all `levelAutBar q M' ζ' γ` with $\zeta'\in$ `Idx q` and $\gamma\in\Gamma_0(M')$. For every $\tau\in G$ preserving `R.integers` and every place $Q$, membership of $Q$ in `NIg` is equivalent to membership of `R.resAut τ` applied to $Q$; and for such $\tau$ and $Q\notin$ `NIg`, the translate `RegularProlongation.smulDisc τ (Dx Q)`, namely the set of places $P$ with $\tau^{-1}\cdot P\in D_Q$, equals the disc attached to `R.resAut τ` applied to $Q$.
--
--   Seventh, discs on distinct Igusa components are disjoint: if $g\in G$ does not preserve `OIg (lineInfty q)` under preimage, then for $Q,Q'\notin$ `NIg` and $P\in D_Q$ one has $g\cdot P\notin D_{Q'}$.
--
--   Eighth, no disc meets the supersingular locus: for $Q\notin$ `NIg`, $P\in D_Q$ and $s\in W$ it is not the case that both of the following hold, where $j$ and $j_{M'}$ denote the images in `fieldBar q M'` of the coefficient embeddings of `jq` and of `qExpand ℚ M' jq`: first, $j$ lies in the valuation subring of $P$ and for every $a\in A$ whose residue is the value of $s$ at `jGeomGen κ M'` the difference of the $P$-value of $j$ and $a$ lies in $A$ and in its maximal ideal; second, the same statement for $j_{M'}$ with `jNGeomGen κ M'` in place of `jGeomGen κ M'`.
--
--   Ninth, conversely the discs cover the non-supersingular places up to the level automorphisms: for every place $P$ of `fieldBar q M'` over $\overline{\mathbb Q}$, if for every $s\in W$ it fails that (for every $f\in$ `R₀.integers` whose order is non-negative at every place where the coefficient embedding of `jq` has non-negative order, with $R_0$-residue in the valuation subring of $s$, and every $a\in A$ whose residue is the value of $s$ at that $R_0$-residue, the difference of the $P$-value of the image of $f$ and $a$ lies in $A$ and in its maximal ideal), then there are $\gamma\in\Gamma_0(M')$ and $Q\notin$ `NIg` with `levelAutBar q M' ζ γ` $\cdot P\in D_Q$.
--
--   Finally, there is a place $P$ of `fieldBar q M'` over $\overline{\mathbb Q}$ whose valuation subring is `qIntegersBar`, the set of elements whose Laurent series has non-negative order, together with a $Q\notin$ `NIg` such that $P\in D_Q$.
--
--   This is the Igusa-component counterpart of the supersingular chart theorem: it produces, on the Gauss ring at the cusp $\infty$ of $X(\Gamma_H(q^2M'))$, a formally smooth local chart with its residue disc at every place of the reduced field outside a set of nodes in bijection with the supersingular places of $X_0(M')_\kappa$, together with the equivariance of the whole package under inertia at $q$ and under the level automorphisms. It is cited by [`ModularCurve.FullLevel.exists_igusaNodes_discFamily_of_igusaGaussRing_allInertia`](thm.html#ModularCurve.FullLevel.exists_igusaNodes_discFamily_of_igusaGaussRing_allInertia) in the construction of the semistable model of the modular curve of level $q^2M'$ over $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaSmoothPointCharts_of_igusaGaussRing_allInertia.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_igusaSmoothPointCharts_of_igusaGaussRing_allInertia
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
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A) :
    ∃ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))))
      (Sx : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Subring ↥(fieldBar q M'))
      (φx : (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) → (Polynomial ↥A →+* ↥(Sx Q)))
      (χ₀x : (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) → (↥(Sx Q) →+* ResidueField ↥A))
      (Dx : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
      NIg.card = W.card ∧

      (∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg →

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

      (∀ Q Q' : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → Q' ∉ NIg → ∀ P, P ∈ Dx Q → P ∈ Dx Q' → Q = Q') ∧

      (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ Q, Q ∉ NIg →
        (∀ f : fieldBar q M', f ∈ Sx Q ↔
          ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ Sx Q) ∧
        (∀ (f : ↥(Sx Q)) (hf : ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : fieldBar q M') ∈ Sx Q),
          χ₀x Q ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : fieldBar q M'), hf⟩ = χ₀x Q f)) ∧

      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) ∧
      (∀ τ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
        R.resAut τ hτ • Q ∈ NIg ↔ Q ∈ NIg) ∧
      (∀ τ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
        Q ∉ NIg → RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q)) ∧

      (∀ g ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), (OIg (lineInfty q)).comap g.toAlgHom.toRingHom ≠ OIg (lineInfty q) →
        ∀ Q Q', Q ∉ NIg → Q' ∉ NIg → ∀ P, P ∈ Dx Q → g • P ∉ Dx Q') ∧

      (∀ Q, Q ∉ NIg → ∀ P ∈ Dx Q, ∀ s : ↥W, ¬ (((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
          (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField A) M') →
            ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ maximalIdeal A)) ∧
        ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
          (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jNGeomGen (ResidueField A) M') →
            ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ maximalIdeal A)))) ∧

      (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
        (∀ s : ↥W, ¬ (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              ∀ a : A, residue A a =
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A)) →
        ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ ∃ Q, Q ∉ NIg ∧ levelAutBar q M' ζ γ • P ∈ Dx Q) ∧
      ∃ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P.toValuationSubring = qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M') ∧
        ∃ Q, Q ∉ NIg ∧ P ∈ Dx Q := by sorry
