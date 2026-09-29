-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert
-- name    : ModularCurve.FullLevel.igusaDiscs_inertia_stable_of_stalkInert
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/763afc42-4386-501e-a832-4ec8b0637ac5
-- title:
--   Tame inertia stabilises the transported Igusa discs
-- statement:
--   Fix a prime $q$ with $5 \le q$ and a natural number $M' \neq 0$ with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a nonunit of $A$. Write $k =$ `ResidueField A`. Let $W$ be a finite set of places of `modularFunctionFieldC k M'` over $k$, and let `hW` say that $W$ consists exactly of the supersingular places `ssPlaces q M' k`, that is, the rational places lying on the affine geometric locus whose value at the geometric $j$-generator lies in the supersingular $j$-set. Let `hle` be the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'` of the base-changed function field of full level $M'$ into `fieldBar q M' = xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`.
--
--   The reduction data consist of a `ConstantReduction` $R_0$ for $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC k M'` (a valuation subring `R₀.integers`, a surjective residue map onto the reduced field with kernel the maximal ideal, compatible with $A$ and with reduction of constants, together with the scaling and divisor-pushforward clauses of that structure), and the hypothesis `hR₀`: for every Laurent series $y$ over $A$ whose coefficientwise image in `LaurentSeries` $\overline{\mathbb{Q}}$ lies in `modularFunctionFieldBar M'`, that image lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over $k$, is the coefficientwise reduction of $y$ along $A \to k$.
--
--   Further data: an index $\zeta \in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$), a family $O_{\mathrm{Ig}}$ of valuation subrings of `fieldBar q M'` indexed by the projective line [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) over $\mathbb{Z}/q$, and a family $O_{\mathrm{SS}}$ of valuation subrings indexed by $W$.
--
--   The Igusa-chart hypotheses are: `hIg_inf`, which describes $O_{\mathrm{Ig}}(\infty)$ at the line `lineInfty q` as the set of $f$ for which there are Laurent series $x, y$ over $A$ with the reduction of $y$ nonzero and $f \cdot y = x$ after coefficientwise inclusion $A \hookrightarrow \overline{\mathbb{Q}}$; `hIg`, which for each line $\ell$ produces $\gamma \in \Gamma_0(M')$ whose reduction `redQ q γ` carries `lineInfty q` to $\ell$ and for which $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ`; `hIg_inj`, the injectivity of $\ell \mapsto O_{\mathrm{Ig}}(\ell)$; and `hIg_perm`, which says that for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the pullback along `levelAutBar q M' ζ' γ` permutes the family $O_{\mathrm{Ig}}$ along some permutation of the projective line.
--
--   The supersingular-chart hypotheses are: `hSS_A`, that for each $s \in W$ and $x \in \overline{\mathbb{Q}}$ the image of $x$ lies in $O_{\mathrm{SS}}(s)$ exactly when $x \in A$; `hSS_over`, which for $s \in W$ and $f \in$ `R₀.integers` such that $f$ has nonnegative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ at which the coefficientwise image of the $q$-expansion `jq` has nonnegative order, and such that the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, asserts both that the image of $f$ under `IntermediateField.inclusion hle` lies in $O_{\mathrm{SS}}(s)$ and that for every $a \in A$ whose reduction in $k$ equals the value $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference between that image and the image of $a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$; `hSS_fix`, that each $O_{\mathrm{SS}}(s)$ is its own pullback along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; and `hSS_tr`, which provides for each $s$ an element $t \in O_{\mathrm{SS}}(s)$ such that $t$ minus the image of any $a \in A$ is a unit of $O_{\mathrm{SS}}(s)$.
--
--   Next, an element $\pi \in \overline{\mathbb{Q}}$ with $\pi^{q^2 - 1} = q$ and $\pi \in A$.
--
--   The chart data at $\infty$: a family $C_{\mathrm{Ig}}$ of `ComponentChart`s for $A$ on `fieldBar q M'` with values in `xHFunctionFieldC k (q ^ 2 * M') (levelH q M')`, indexed by the projective line; a distinguished chart $C_\infty$; a `RegularProlongation` $R_I$ with `RI.integers = OIg (lineInfty q)` (`hRI`); the agreements `hCinfint`, that $C_\infty$ and $R_I$ have the same ring of integers, and `hCinfres`, that their residue maps agree on common elements. Further, a finite set $N_{\mathrm{Ig}}$ of places of `xHFunctionFieldC k (q ^ 2 * M') (levelH q M')` over $k$, a disc assignment $\mathrm{disc}_I$ sending such places to sets of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$, and a coordinate assignment $\mathrm{coord}_I$, subject to `hnodesI`, that the nodes of $C_\infty$ are $N_{\mathrm{Ig}}$, and `hfamI`, that `RI.DiscFamily NIg discI coordI` holds, i.e. for each $Q \notin N_{\mathrm{Ig}}$ the set $\mathrm{disc}_I(Q)$ is a residue disc with coordinate $\mathrm{coord}_I(Q)$ and distinct such $Q$ have disjoint discs.
--
--   The stalk data: subrings $S_I(Q)$ of `fieldBar q M'` and ring homomorphisms $\chi_{0,I}(Q) : S_I(Q) \to k$, subject to `hstalkI`: for every $Q \notin N_{\mathrm{Ig}}$, every element of $S_I(Q)$ lies in `RI.integers`, and a place $P$ lies in $\mathrm{disc}_I(Q)$ if and only if $P$ is rational, every $f \in S_I(Q)$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f) \in A$, and for every $f \in S_I(Q)$ one has $A$-valuation of $P.\mathrm{evalAt}(f)$ less than $1$ precisely when $\chi_{0,I}(Q)(f) = 0$. The chart-compatibility hypotheses `hdomI`, `hpmI` and `hpmI_off` state that the domain of $C_\infty$ is the union of the $\mathrm{disc}_I(Q)$ over $Q \notin N_{\mathrm{Ig}}$, that the place map of $C_\infty$ sends $\mathrm{disc}_I(Q)$ to $Q$ for such $Q$, and that this place map is constant off the domain of $C_\infty$.
--
--   Equivariance under the level group: let $\Gamma$ be the subgroup of $\overline{\mathbb{Q}}$-algebra automorphisms of `fieldBar q M'` generated by the automorphisms `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$ and $\zeta'$ arbitrary. The hypothesis `hNstabI` says that for $\tau \in \Gamma$ preserving `RI.integers` the induced residue automorphism `RI.resAut τ` permutes places so that $\mathrm{resAut}\,\tau \cdot Q \in N_{\mathrm{Ig}}$ iff $Q \in N_{\mathrm{Ig}}$; `hdiscstabI` says that for such $\tau$ and $Q \notin N_{\mathrm{Ig}}$ the transported disc `RegularProlongation.smulDisc τ (discI Q)` equals $\mathrm{disc}_I(\mathrm{resAut}\,\tau \cdot Q)$. The transport hypotheses are `g` together with `hg`, assigning to each line $\ell$ an automorphism $g(\ell) \in \Gamma$ which equals `levelAutBar q M' ζ γ` for some $\gamma \in \Gamma_0(M')$ with `redQ q γ • lineInfty q = ℓ`, and `hCIg_def`, that $C_{\mathrm{Ig}}(\ell)$ is the pullback $C_\infty$`.comap (g ℓ)`.
--
--   Finally, the inertia hypotheses: `hSI_inert` states that for every $\tau$ in `A.inertiaSubgroupIn ℚ` with `A.tameCharacter π τ = 1` and every $Q \notin N_{\mathrm{Ig}}$, an element $f$ of `fieldBar q M'` lies in $S_I(Q)$ if and only if its image under the semilinear automorphism [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54) (coefficientwise action of $\tau$ on Laurent series) lies in $S_I(Q)$; and `hχ₀I_inert` states that $\chi_{0,I}(Q)$ is invariant under this action on $S_I(Q)$.
--
--   Under these hypotheses the conclusion is: for every $\tau \in$ `A.inertiaSubgroupIn ℚ` with `A.tameCharacter π τ = 1`, for every line $\ell$ and every place $Q \notin N_{\mathrm{Ig}}$, and for every place $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$, the membership $P \in \{P \mid g(\ell) \cdot P \in \mathrm{disc}_I(Q)\}$ holds if and only if [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P`](def/ModularCurve_ArithmeticGalois.html#L54) lies in that same set; equivalently, $g(\ell) \cdot P \in \mathrm{disc}_I(Q)$ if and only if $g(\ell) \cdot (\tau \cdot P) \in \mathrm{disc}_I(Q)$, where $\tau$ acts through the coefficientwise semilinear automorphism.
--
--   A step in the assembly of the semistable covering of the modular curve $X_{\Gamma_H(q^2M')}$ at a place above $q$: the residue discs of the $\infty$-chart, transported along the level automorphisms $g(\ell)$ to the Igusa charts, are shown to be stable under the part of inertia at $A$ on which the tame character at $\pi$ is trivial. It is used by [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted), and rests on the description of the discs as the loci cut out by the stalk subrings $S_I(Q)$ and their residue characters together with the commutation of such inertia elements with the level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert.lean

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

theorem ModularCurve.FullLevel.igusaDiscs_inertia_stable_of_stalkInert
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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
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

    (hSI_inert : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
      (h1 : A.tameCharacter π τ = 1) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hQ : Q ∉ NIg)
      (f : fieldBar q M'), f ∈ SI Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ SI Q)
    (hχ₀I_inert : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
      (h1 : A.tameCharacter π τ = 1) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hQ : Q ∉ NIg)
      (f : ↥(SI Q)), χ₀I Q ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : fieldBar q M'), (hSI_inert τ hτ h1 Q hQ (f : fieldBar q M')).mp f.2⟩ = χ₀I Q f) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ ℓ Q, Q ∉ NIg → ∀ P, P ∈ {P | g ℓ • P ∈ discI Q} ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ {P | g ℓ • P ∈ discI Q} := by sorry
