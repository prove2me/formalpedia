-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaNodes_discFamily_of_igusaGaussRing_allInertia
-- name    : ModularCurve.FullLevel.exists_igusaNodes_discFamily_of_igusaGaussRing_allInertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/566062db-82d0-5760-aab4-4fc5b53d54f7
-- title:
--   Igusa nodes and residue-disc family for the Gauss prolongation
-- statement:
--   Throughout, $q$ is a prime with $5 \le q$, and $M'$ is a nonzero natural number with $q \nmid M'$. Further, $A$ is a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, i.e. $q$ is a non-unit of $A$; write $\kappa =$ `ResidueField A` for its residue field. Two function fields occur: `modularFunctionFieldC κ M'`, the subfield of $\kappa((q))$ generated over $\kappa$ by `jqModC κ` and by `jqNModC κ M'` $=$ `qExpand κ M' (jqModC κ)`, with the two distinguished generators `jGeomGen κ M'` and `jNGeomGen κ M'`; and `xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')`, the $q$-expansion function field over $\kappa$ of the level group [`CohCarrier.GammaH (q ^ 2 * M') (levelH q M')`](def/CohCarrier_Level.html#L133), where `levelH q M'` is the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, i.e. the units congruent to $1$ modulo $q$. Over $\overline{\mathbb Q}$ the corresponding base-changed fields inside $\overline{\mathbb Q}((q))$ are `modularFunctionFieldBar M'` and `fieldBar q M'` $=$ `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, and `hle` is the hypothesis that the first is contained in the second.
--
--   The remaining data are: a finite set $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$, with `hW` asserting that $W$ consists exactly of the elements of `ssPlaces q M' κ`, i.e. of those places $w$ which are rational (the structure map $\kappa \to w$'s residue field is surjective), satisfy `IsAffineGeomPlace κ M' w`, and have $w.\mathrm{evalAt}(\mathtt{jGeomGen}\ \kappa\ M') \in$ `ssJSet q κ`; a `ConstantReduction` $R_0$ of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'`, that is, a valuation subring $R_0.\mathrm{integers}$ of `modularFunctionFieldBar M'` together with a surjective residue homomorphism onto `modularFunctionFieldC κ M'` whose kernel is the maximal ideal, inducing $A \mapsto \kappa$ on constants, with every nonzero element admitting a scalar multiple of nonzero residue, and with a map `placeMap` on places preserving degrees and compatible with push-forward of divisors of elements; the hypothesis `hR₀`, which says that $R_0$ is coefficientwise reduction: whenever a Laurent series $y$ over $A$ has its image under $A \hookrightarrow \overline{\mathbb Q}$ in `modularFunctionFieldBar M'`, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction of $y$; an index $\zeta \in$ `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$; and two families of valuation subrings of `fieldBar q M'`, namely $O^{\mathrm{Ig}} =$ `OIg` indexed by the projective line [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) $= \mathbb P^1(\mathbb Z/q)$ and $O^{\mathrm{ss}} =$ `OSS` indexed by $W$.
--
--   The Igusa-side hypotheses are four. `hIg_inf` identifies $O^{\mathrm{Ig}}(\mathtt{lineInfty}\ q)$ with the Gauss ring: $f$ belongs to it if and only if there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f \cdot y = x$ in $\overline{\mathbb Q}((q))$. `hIg` says that for every $\ell \in \mathbb P^1(\mathbb Z/q)$ there is $\gamma \in \mathrm{SL}_2(\mathbb Z)$ lying in $\Gamma_0(M')$ with `redQ q γ • lineInfty q = ℓ` and $O^{\mathrm{Ig}}(\ell)$ the preimage of $O^{\mathrm{Ig}}(\mathtt{lineInfty}\ q)$ under `levelAutBar q M' ζ γ`. `hIg_inj` says $O^{\mathrm{Ig}}$ is injective, and `hIg_perm` that for every $\zeta' \in$ `Idx q` and every $\gamma \in \Gamma_0(M')$ the preimages under `levelAutBar q M' ζ' γ` permute the family $O^{\mathrm{Ig}}$.
--
--   The supersingular-side hypotheses are four. `hSS_A` says that for each $s$ an element $x \in \overline{\mathbb Q}$ has its image in $O^{\mathrm{ss}}(s)$ exactly when $x \in A$. `hSS_over` says that $O^{\mathrm{ss}}(s)$ specialises to $s$: if $f \in R_0.\mathrm{integers}$ has non-negative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the base-changed $q$-expansion `coeffEmb (AlgebraicClosure ℚ) jq` of $j$ has non-negative order, and if the $R_0$-residue of $f$ lies in the valuation subring of $s$, then the image of $f$ in `fieldBar q M'` lies in $O^{\mathrm{ss}}(s)$, and for every $a \in A$ whose residue in $\kappa$ equals $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference of the image of $f$ and $a$ lies in the maximal ideal of $O^{\mathrm{ss}}(s)$. `hSS_fix` says each $O^{\mathrm{ss}}(s)$ is its own preimage under every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$. `hSS_tr` provides, for each $s$, an element $t \in O^{\mathrm{ss}}(s)$ such that $t - a$ is a unit of $O^{\mathrm{ss}}(s)$ for every $a \in A$.
--
--   Finally, $R$ is a `RegularProlongation` of $A$ from `fieldBar q M'` to `xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')`, that is, a valuation subring $R.\mathrm{integers}$ with a surjective residue homomorphism onto that $\kappa$-field, kernel the maximal ideal, inducing $A \mapsto \kappa$ on constants, and with every nonzero element admitting a scalar multiple of nonzero residue; `hR` identifies $R.\mathrm{integers}$ with $O^{\mathrm{Ig}}(\mathtt{lineInfty}\ q)$, and `hR₀O` says that $f \in R_0.\mathrm{integers}$ if and only if the image of $f$ in `fieldBar q M'` lies in $O^{\mathrm{Ig}}(\mathtt{lineInfty}\ q)$. In addition, $\pi \in \overline{\mathbb Q}$ satisfies $\pi^{q^2-1} = q$ and $\pi \in A$.
--
--   Under these hypotheses there exist a finite set $N =$ `NIg` of places of `xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')` over $\kappa$, an assignment $Q \mapsto \mathrm{disc}(Q)$ of a set of places of `fieldBar q M'` over $\overline{\mathbb Q}$, an assignment $Q \mapsto \mathrm{coord}(Q) \in$ `fieldBar q M'`, an assignment $Q \mapsto S(Q)$ of a subring of `fieldBar q M'`, and for each $Q$ a ring homomorphism $\chi_0^Q : S(Q) \to \kappa$, such that all of the following hold.
--
--   (i) $N$ and $W$ have the same cardinality.
--
--   (ii) `R.DiscFamily NIg disc coord` holds: for every $Q \notin N$ the triple satisfies `R.IsResidueDisc Q (disc Q) (coord Q)`, i.e. the three conditions `R.IsDiscCoord Q (disc Q) (coord Q)`, `R.PointwiseOn Q (disc Q)` and `R.DegreeOn Q (disc Q)`; and if $Q, Q' \notin N$ and some place $P$ lies in both $\mathrm{disc}(Q)$ and $\mathrm{disc}(Q')$ then $Q = Q'$.
--
--   (iii) For every $Q \notin N$: every element of $S(Q)$ lies in $R.\mathrm{integers}$, and a place $P$ lies in $\mathrm{disc}(Q)$ if and only if $P$ is rational, every $f \in S(Q)$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f) \in A$, and for every $f \in S(Q)$ the $A$-valuation of $P.\mathrm{evalAt}(f)$ is $< 1$ precisely when $\chi_0^Q(f) = 0$.
--
--   (iv) For every $\tau$ in `A.inertiaSubgroupIn ℚ` (the image in $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup of $A$ inside its decomposition subgroup) and every $Q \notin N$: the subring $S(Q)$ is stable in both directions under the coefficientwise semilinear action `arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ` on `fieldBar q M'`, and $\chi_0^Q$ is invariant under that action.
--
--   (v) There is a ring homomorphism $j$ from `modularFunctionFieldC κ M'` to `xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')` such that: for every $f \in R_0.\mathrm{integers}$ the image of $f$ in `fieldBar q M'` lies in $R.\mathrm{integers}$ and its $R$-residue is $j$ applied to the $R_0$-residue of $f$; and $Q \in N$ if and only if there is $s \in W$ with $g$ in the valuation subring of $s$ exactly when $j(g)$ is in the valuation subring of $Q$, for all $g$ in `modularFunctionFieldC κ M'`.
--
--   (vi) For every $\tau$ in the subgroup of $\overline{\mathbb Q}$-algebra automorphisms of `fieldBar q M'` generated by the automorphisms `levelAutBar q M' ζ' γ` with $\zeta' \in$ `Idx q` and $\gamma \in \Gamma_0(M')$, and for any proof that $\tau$ preserves $R.\mathrm{integers}$, the induced automorphism `R.resAut τ` of the residue field over $\kappa$ acts on places preserving $N$: $\mathtt{R.resAut}\,\tau \cdot Q \in N$ if and only if $Q \in N$.
--
--   (vii) For $\tau$ in the same subgroup, preserving $R.\mathrm{integers}$, and for $Q \notin N$: `RegularProlongation.smulDisc τ (disc Q)`, i.e. the set of places $P$ with $\tau^{-1} \cdot P \in \mathrm{disc}(Q)$, equals $\mathrm{disc}(\mathtt{R.resAut}\,\tau \cdot Q)$.
--
--   (viii) For every $g$ in that subgroup whose preimage of $O^{\mathrm{Ig}}(\mathtt{lineInfty}\ q)$ is different from $O^{\mathrm{Ig}}(\mathtt{lineInfty}\ q)$, and all $Q, Q' \notin N$: if $P \in \mathrm{disc}(Q)$ then $g \cdot P \notin \mathrm{disc}(Q')$.
--
--   (ix) For every $Q \notin N$, every $P \in \mathrm{disc}(Q)$ and every $s \in W$, it is not the case that both of the following hold: the image in `fieldBar q M'` of the element `coeffEmb (AlgebraicClosure ℚ) jq` of `modularFunctionFieldBar M'` lies in the valuation subring of $P$ and, for every $a \in A$ whose residue equals $s.\mathrm{evalAt}(\mathtt{jGeomGen}\ \kappa\ M')$, the difference $P.\mathrm{evalAt}$ of that element minus $a$ lies in the maximal ideal of $A$; and the same two conditions with `coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq)` in place of `coeffEmb (AlgebraicClosure ℚ) jq` and `jNGeomGen κ M'` in place of `jGeomGen κ M'`.
--
--   (x) For every place $P$ of `fieldBar q M'` over $\overline{\mathbb Q}$ which for no $s \in W$ satisfies the specialisation condition "for every $f \in R_0.\mathrm{integers}$ of non-negative order at all places where `coeffEmb (AlgebraicClosure ℚ) jq` has non-negative order, whose $R_0$-residue lies in the valuation subring of $s$, and for every $a \in A$ with residue $s.\mathrm{evalAt}$ of that $R_0$-residue, the element $P.\mathrm{evalAt}$ of the image of $f$ minus $a$ lies in the maximal ideal of $A$", there exist $\gamma \in \Gamma_0(M')$ and $Q \notin N$ with `levelAutBar q M' ζ γ • P ∈ disc Q`.
--
--   (xi) There exists a place $P$ of `fieldBar q M'` over $\overline{\mathbb Q}$ whose valuation subring is `qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M')`, the subring of elements of non-negative order as Laurent series, together with some $Q \notin N$ with $P \in \mathrm{disc}(Q)$.
--
--   This is the Igusa-side node and residue-disc law for a semistable covering of the modular curve of level [`CohCarrier.GammaH (q ^ 2 * M') (levelH q M')`](def/CohCarrier_Level.html#L133) at a place of $\overline{\mathbb Q}$ above $q$: the reduction of the Gauss valuation ring at the cusp $\infty$ has exactly $|W|$ nodes, one above each supersingular place of level $M'$, and its smooth locus is covered by an equivariant family of residue discs. It feeds the assembly of the semistable covering in [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaNodes_discFamily_of_igusaGaussRing_allInertia.lean

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
set_option maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.exists_igusaNodes_discFamily_of_igusaGaussRing_allInertia
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
      (disc : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
      (coord : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → (fieldBar q M'))
      (S : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Subring (fieldBar q M'))
      (χ₀ : ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), ↥(S Q) →+* ResidueField A),
      NIg.card = W.card ∧ R.DiscFamily NIg disc coord ∧

      (∀ Q, Q ∉ NIg → (∀ f : ↥(S Q), (f : fieldBar q M') ∈ R.integers) ∧
        ∀ P, P ∈ disc Q ↔ P.IsRational ∧
          (∀ f : ↥(S Q), (f : fieldBar q M') ∈ P.toValuationSubring ∧ P.evalAt (f : fieldBar q M') ∈ A) ∧
          (∀ f : ↥(S Q), A.valuation (P.evalAt (f : fieldBar q M')) < 1 ↔ χ₀ Q f = 0)) ∧

      (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ Q, Q ∉ NIg →
        (∀ f : fieldBar q M', f ∈ S Q ↔
          ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ S Q) ∧
        (∀ (f : ↥(S Q)) (hf : ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : fieldBar q M') ∈ S Q),
          χ₀ Q ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : fieldBar q M'), hf⟩ = χ₀ Q f)) ∧

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
        Q ∉ NIg → RegularProlongation.smulDisc τ (disc Q) = disc (R.resAut τ hτ • Q)) ∧

      (∀ g ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), (OIg (lineInfty q)).comap g.toAlgHom.toRingHom ≠ OIg (lineInfty q) →
        ∀ Q Q', Q ∉ NIg → Q' ∉ NIg → ∀ P, P ∈ disc Q → g • P ∉ disc Q') ∧

      (∀ Q, Q ∉ NIg → ∀ P ∈ disc Q, ∀ s : ↥W, ¬ (((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
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
        ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ ∃ Q, Q ∉ NIg ∧ levelAutBar q M' ζ γ • P ∈ disc Q) ∧
      ∃ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P.toValuationSubring = qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M') ∧
        ∃ Q, Q ∉ NIg ∧ P ∈ disc Q := by sorry
