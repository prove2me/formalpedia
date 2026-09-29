-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_naturality_unipotent_igusaInfty_of_discFamily_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.naturality_unipotent_igusaInfty_of_discFamily_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/ab51e602-f6e1-5d3b-a5d4-2c4f775e4cdb
-- title:
--   Unipotent naturality at the Igusa chart of ∞, q=3
-- statement:
--   Throughout, $q$ is a prime with $q=3$; $M'$ is a nonzero natural number not divisible by $q$; $\ell$ is a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$ (the rigid-level guard); and $A$ is a valuation subring of $\overline{\mathbb Q}$ satisfying `A.LiesOverPrime q`, i.e. $q$ is a nonunit of $A$. Here `fieldBar q M'` is the base change to $\overline{\mathbb Q}$, inside $\overline{\mathbb Q}((t))$, of the function field of $X_H$ of level $q^2M'$ for $H =$ `levelH q M'`, the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$ (the units congruent to $1$ modulo $q$); `xHFunctionFieldC (ResidueField A) (q^2*M') (levelH q M')` is the corresponding $q$-expansion function field over the residue field of $A$, and `modularFunctionFieldC (ResidueField A) M'` is the field generated over that residue field by the $q$-expansions of $j$ and of $j$ at level $M'$. A `Place` of a field extension is a valuation subring, not the whole field, containing the image of the base field and having principal ideals.
--
--   The further data are: a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` which, by `hW`, consists exactly of the members of `ssPlaces q M' (ResidueField A)`, namely the rational affine geometric places whose value at the geometric $j$-coordinate is a supersingular $j$-invariant for $q$; the inclusion `hle` of `modularFunctionFieldBar M'` (the base change to $\overline{\mathbb Q}$ of the full level-$M'$ modular function field over $\mathbb Q$) into `fieldBar q M'`; a constant reduction $R_0$ of `modularFunctionFieldBar M'` along $A$ with reduced field `modularFunctionFieldC (ResidueField A) M'`, i.e. a valuation subring of integers, a surjective residue map onto the reduced field with kernel the maximal ideal, a map on places, and the compatibility axioms of `ConstantReduction`; the hypothesis `hR₀`, which requires that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}((t))$ lies in `modularFunctionFieldBar M'`, that image lies in $R_0$'s ring of integers and its $R_0$-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$; an index $\zeta$ in `Idx q`, that is, a primitive $q$-th root of unity in $\overline{\mathbb Q}$; and two families of valuation subrings of `fieldBar q M'`, one indexed by $\mathbb P^1(\mathbb Z/q)$ (`OIg`) and one by $W$ (`OSS`).
--
--   The Igusa group of hypotheses is: `hIg_inf`, which says that $f$ lies in `OIg (lineInfty q)`, at the point $(1:0)$ of $\mathbb P^1(\mathbb Z/q)$, precisely when there are Laurent series $x,y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f\cdot y = x$ coefficientwise; `hIg`, which provides for every point of the projective line a matrix $\gamma \in \Gamma_0(M')$ whose reduction `redQ q γ` carries $(1:0)$ to that point and for which the ring attached to the point is the pullback of `OIg (lineInfty q)` along `levelAutBar q M' ζ γ`; `hIg_inj`, the injectivity of `OIg`; and `hIg_perm`, which says that for every $\zeta'$ in `Idx q` and every $\gamma \in \Gamma_0(M')$ the pullbacks along `levelAutBar q M' ζ' γ` permute the family `OIg` according to some permutation of $\mathbb P^1(\mathbb Z/q)$. (In `hIg`, `hIg_perm`, `hg` and `hCIg_def` the bound point of the projective line is written `ℓ`, shadowing the prime $\ell$.)
--
--   The supersingular group of hypotheses is: `hSS_A`, that a constant from $\overline{\mathbb Q}$ lies in `OSS s` exactly when it lies in $A$; `hSS_over`, which states that for $s \in W$ and $f$ in the ring of integers of $R_0$ such that $f$ has nonnegative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the coefficient embedding of the $q$-expansion `jq` has nonnegative order, and such that the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, the image of $f$ in `fieldBar q M'` lies in `OSS s`, and moreover for every $a \in A$ whose residue equals the value at $s$ of the $R_0$-residue of $f$, the difference of that image and the constant $a$ lies in `OSS s` and in the maximal ideal of `OSS s`; `hSS_fix`, that each `OSS s` is its own pullback along `levelAutBar q M' ζ' γ` for all $\zeta'$ in `Idx q` and all $\gamma \in \Gamma_0(M')$; and `hSS_tr`, that each `OSS s` contains an element $t$ such that $t$ minus any constant from $A$ is a unit of `OSS s`.
--
--   The charted group of hypotheses concerns component charts with reduced field `xHFunctionFieldC (ResidueField A) (q^2*M') (levelH q M')`; a `ComponentChart` consists of a valuation subring of `fieldBar q M'` inducing $A$ on constants, a surjective residue map onto the reduced field with kernel the maximal ideal, a set `dom` of places, a finite set `nodes` of places of the reduced field, a place map, and the pointwise and divisor-compatibility axioms. The data are: a family `CIg` of such charts indexed by $\mathbb P^1(\mathbb Z/q)$; a chart `Cinf`; a regular prolongation `RI` (the same data without `dom`, `nodes` and place map) whose ring of integers is `OIg (lineInfty q)` by `hRI`, with `hCinfint` saying that `Cinf` has that same ring of integers and `hCinfres` that the two residue maps agree; a finite set `NIg` of places of the reduced field, a map `discI` assigning to each such place a set of places of `fieldBar q M'` over $\overline{\mathbb Q}$, and a coordinate map `coordI`, subject to `hnodesI` (the nodes of `Cinf` are `NIg`) and `hfamI` (`RI.DiscFamily NIg discI coordI`: for every $Q \notin NIg$ the set `discI Q` is a residue disc for `RI` with coordinate `coordI Q`, and two places outside `NIg` with a common member of their discs coincide); a family `SI` of subrings of `fieldBar q M'` and ring homomorphisms `χ₀I` from each `SI Q` to the residue field of $A$, subject to `hstalkI`: for $Q \notin NIg$, every element of `SI Q` lies in the ring of integers of `RI`, and a place $P$ lies in `discI Q` exactly when $P$ is rational, every $f \in SI\,Q$ lies in the valuation subring of $P$ with $P$-value in $A$, and for every such $f$ the $A$-valuation of that value is $<1$ precisely when `χ₀I Q f = 0`; `hdomI`, that the domain of `Cinf` is the union of the discs `discI Q` over $Q \notin NIg$; `hpmI`, that the place map of `Cinf` sends every $P \in$ `discI Q` to $Q$ for $Q \notin NIg$; `hpmI_off`, that the place map of `Cinf` is constant outside its domain; `hNstabI` and `hdiscstabI`, which require, for every $\tau$ in the subgroup generated by the automorphisms `levelAutBar q M' ζ γ` with $\zeta$ in `Idx q` and $\gamma \in \Gamma_0(M')$ that preserves the ring of integers of `RI` in both directions, that the induced automorphism `RI.resAut τ` of the reduced field preserves `NIg` and that for $Q \notin NIg$ the translate `RegularProlongation.smulDisc τ (discI Q)`, namely $\{P : \tau^{-1}\cdot P \in \mathrm{discI}\,Q\}$, is `discI` of the translate of $Q$; and finally a family $g$ of automorphisms of `fieldBar q M'` over $\overline{\mathbb Q}$ with `hg`, requiring each $g$-value to lie in that subgroup and to be of the form `levelAutBar q M' ζ γ` for some $\gamma \in \Gamma_0(M')$ whose reduction carries $(1:0)$ to the given point, together with `hCIg_def`, which identifies each `CIg` chart with the pullback `Cinf.comap (g ℓ)` of the chart at $\infty$.
--
--   The last hypothesis `huni` is the unipotent clause at the Igusa chart of $\infty$: for every $\zeta'$ in `Idx q` and every $\gamma \in \Gamma_0(M')$ whose reduction `redQ q γ` equals [`CuspidalType.unipotent q t`](def/CuspidalType_IsCuspidalOfType.html#L27) for some $t \in \mathbb Z/q$, the semilinear automorphism `SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹)` — the pair consisting of `levelAutBar q M' ζ' γ⁻¹` and the identity of $\overline{\mathbb Q}$ — induces on the chart `CIg (lineInfty q)` with the identity automorphism of the reduced field, that is, membership in the chart's ring of integers is equivalent for $f$ and for its translate, and the residue of the translate of $f$ equals the residue of $f$.
--
--   The conclusion is that for every $\zeta'$ in `Idx q` and every $\gamma \in \Gamma_0(M')$ whose reduction is unipotent, `redQ q γ = CuspidalType.unipotent q t` for some $t \in \mathbb Z/q$, the following three statements hold for the semilinear automorphism $g_0 =$ `SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹)` and the chart `CIg (lineInfty q)`: first, a place $P$ lies in the domain of that chart if and only if $g_0 \cdot P$ does; second, $g_0$ induces on the chart with the identity ring automorphism of the reduced field, which is the hypothesis `huni` restated at the same pair $(\zeta',\gamma)$; third, for every $P$ in the domain of the chart, the chart's place map sends $g_0 \cdot P$ and $P$ to the same place of the reduced field.
--
--   This is one of the naturality clauses used in assembling the semistable covering of $X_H(q^2M')$ in the case $q = 3$: it says that the level automorphisms with unipotent reduction modulo $q$ act on the Igusa chart at the cusp $\infty$ without moving its domain or its place map. It is invoked in the existence theorem for the semistable covering, [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd), and its proof uses the multiplicativity of `levelAutBar` on $\Gamma_0(M')$ and the invariance of the Igusa ring at $\infty$ under the automorphisms fixing the point $(1:0)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_naturality_unipotent_igusaInfty_of_discFamily_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois

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

theorem ModularCurve.FullLevel.naturality_unipotent_igusaInfty_of_discFamily_of_eq_three_of_dvd
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
    (CIg : CuspidalType.ProjLine q → ComponentChart A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (Cinf : ComponentChart A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (RI : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hRI : RI.integers = OIg (lineInfty q))
    (hCinfint : Cinf.integers = RI.integers)
    (hCinfres : ∀ (f : fieldBar q M') (hC : f ∈ Cinf.integers) (hR : f ∈ RI.integers), Cinf.residue ⟨f, hC⟩ = RI.residue ⟨f, hR⟩)
    (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))))
    (discI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
    (coordI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → (fieldBar q M'))
    (hnodesI : Cinf.nodes = NIg) (hfamI : RI.DiscFamily NIg discI coordI)
    (SI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Subring (fieldBar q M'))
    (χ₀I : ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), ↥(SI Q) →+* ResidueField A)
    (hstalkI : (∀ Q, Q ∉ NIg → (∀ f : ↥(SI Q), (f : fieldBar q M') ∈ RI.integers) ∧
        ∀ P, P ∈ discI Q ↔ P.IsRational ∧
          (∀ f : ↥(SI Q), (f : fieldBar q M') ∈ P.toValuationSubring ∧ P.evalAt (f : fieldBar q M') ∈ A) ∧
          (∀ f : ↥(SI Q), A.valuation (P.evalAt (f : fieldBar q M')) < 1 ↔ χ₀I Q f = 0)))
    (hdomI : ∀ P, P ∈ Cinf.dom ↔ ∃ Q, Q ∉ NIg ∧ P ∈ discI Q)
    (hpmI : ∀ P Q, Q ∉ NIg → P ∈ discI Q → Cinf.placeMap P = Q)
    (hpmI_off : ∀ P P', P ∉ Cinf.dom → P' ∉ Cinf.dom → Cinf.placeMap P = Cinf.placeMap P')
    (hNstabI : ∀ τ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ RI.integers ↔ f ∈ RI.integers)
      (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))), RI.resAut τ hτ • Q ∈ NIg ↔ Q ∈ NIg)
    (hdiscstabI : ∀ τ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ RI.integers ↔ f ∈ RI.integers)
      (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))), Q ∉ NIg → RegularProlongation.smulDisc τ (discI Q) = discI (RI.resAut τ hτ • Q))
    (g : CuspidalType.ProjLine q → ((fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')))
    (hg : ∀ ℓ, g ℓ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}) ∧ ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧ g ℓ = levelAutBar q M' ζ γ)
    (hCIg_def : ∀ ℓ, CIg ℓ = Cinf.comap (g ℓ))

    (huni : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (∃ t : ZMod q, redQ q γ = CuspidalType.unipotent q t) →
      SemistableCovering.InducesOnChart (CIg (lineInfty q)) (SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹)) (RingEquiv.refl _)) :
    ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (∃ t : ZMod q, redQ q γ = CuspidalType.unipotent q t) →
      (∀ P, P ∈ (CIg (lineInfty q)).dom ↔ SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹) • P ∈ (CIg (lineInfty q)).dom) ∧
      SemistableCovering.InducesOnChart (CIg (lineInfty q)) (SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹)) (RingEquiv.refl _) ∧
      (∀ P ∈ (CIg (lineInfty q)).dom,
        (CIg (lineInfty q)).placeMap (SemilinearAut.ofAlgAut (levelAutBar q M' ζ' γ⁻¹) • P) = (CIg (lineInfty q)).placeMap P) := by sorry
