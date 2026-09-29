-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_levelAut_transitive_ends_moves_smoothPlaces
-- name    : ModularCurve.FullLevel.supersingularProlongation_levelAut_transitive_ends_moves_smoothPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/53b6f4fb-ba61-5960-9ace-99ba9f94a862
-- title:
--   Level automorphisms: transitive on ends, no fixed smooth place
-- statement:
--   Throughout, $q$ is a prime with $5 \le q$, $M'$ is a nonzero natural number with $q \nmid M'$, and $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `hA : A.LiesOverPrime q`, i.e. $q$ lies in the nonunits of $A$; $\kappa =$ `ResidueField A` denotes its residue field. Places of an extension $F/K$ are understood in the sense of the project's structure `Place`: valuation subrings of $F$ containing the image of $K$, distinct from $F$ itself and with principal ideal ring of integers; `ord` is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation, `IsRational` means that $K$ surjects onto the residue field of the place, and `evalAt` is the residue map followed by a chosen inverse of $K \to$ residue field (and $0$ off the valuation subring).
--
--   The level-$M'$ side of the data. `modularFunctionFieldBar M'` is the base change to $\overline{\mathbb{Q}}$ of `modularFunctionFieldFull M'` inside Laurent series, and `modularFunctionFieldC κ M'` is the subfield $\kappa(\,$`jqModC`$,$`jqNModC`$\,)$ of `LaurentSeries κ`. A finite set $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$ is given, and `hW` states that $W$ consists exactly of the supersingular places `ssPlaces q M' κ`, i.e. of those places $w$ that are rational, are affine geometric places, and satisfy $w(\,$`jGeomGen`$\,) \in$ `ssJSet q κ`. A distinguished element $s \in W$ is fixed. Further, `hle` asserts the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'`, where `fieldBar q M'` is the base change to $\overline{\mathbb{Q}}$ of the level-$H$ function field of level $q^2M'$ for the subgroup `levelH q M'` of $(\mathbb{Z}/q^2M')^\times$ (a kernel of a unit-group reduction map). A `ConstantReduction` $R_0$ of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` is given, that is: a valuation subring $R_0.$`integers`, a surjective residue homomorphism onto `modularFunctionFieldC κ M'` with kernel the maximal ideal, compatibility with $A$ and with its residue map, the scaling property that every nonzero element becomes a unit after multiplication by a suitable constant, and a place map preserving degrees and orders. The hypothesis `hR₀` identifies $R_0$ with coefficientwise reduction: for every Laurent series $y$ over $A$ whose image under `coeffMap A.subtype` lies in `modularFunctionFieldBar M'`, that image lies in $R_0.$`integers` and its $R_0$-residue, read as a Laurent series over $\kappa$, equals `coeffMap (IsLocalRing.residue A) y`.
--
--   The supersingular component and its charts. There are given a field `FSS` over $\kappa$, a `RegularProlongation` $R$ of $A$ from `fieldBar q M'` to `FSS` (a valuation subring $R.$`integers` with surjective residue map onto `FSS` whose kernel is the maximal ideal, compatible with $A$, and with the same scaling property), a finite set $N$ of places of `FSS` over $\kappa$, and, indexed by places $Q$ of `FSS` over $\kappa$, a subring $S_Q \subseteq$ `fieldBar q M'`, a ring homomorphism $\varphi_Q \colon A[T] \to S_Q$, a ring homomorphism $\chi_{0,Q} \colon S_Q \to \kappa$, and a set $D_Q$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$. These satisfy:
--
--   `h0`: `FSS` contains an element transcendental over $\kappa$.
--
--   `h1` ($R$ lies over $s$): for every $f$ in `modularFunctionFieldBar M'` belonging to $R_0.$`integers` such that $f$ has nonnegative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ at which the coefficient image of `jq` has nonnegative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` lies in $R.$`integers` and its $R$-residue equals the image in `FSS` of the value $s(\,$$R_0$-residue of $f$$\,) \in \kappa$.
--
--   `h2`: for every $\zeta \in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in \Gamma_0(M')$, the pullback of $R.$`integers` along `levelAutBar q M' ζ γ` is $R.$`integers`.
--
--   `hcard`: $N$ has exactly $q+1$ elements.
--
--   `hpkg` (fourteen clauses, summarised here): for every place $Q \notin N$ the tuple $(S_Q, \varphi_Q, \chi_{0,Q}, D_Q)$ is a smooth-point package: $S_Q$ contains the image of $A$; $\varphi_Q$ is formally smooth and formally unramified, sends constants $C(a)$ to the image of $a$, and satisfies $\chi_{0,Q}(\varphi_Q(C(a))) = \bar a$ and $\chi_{0,Q}(\varphi_Q(T)) = 0$; for every $c$ in the maximal ideal of $A$ there is a unique $A$-section $\chi \colon S_Q \to A$ of $\varphi_Q \circ C$ reducing to $\chi_{0,Q}$ with $\chi(\varphi_Q(T)) = c$; every element of $S_Q$ lies in $R.$`integers`, its $R$-residue lies in the valuation subring of $Q$ and reduces there to the image of its $\chi_{0,Q}$-value; the $R$-residue of $\varphi_Q(T)$ has order $1$ at $Q$; $D_Q$ consists exactly of the rational places $P$ at which all elements of $S_Q$ are integral with values in $A$, and at which the values of valuation $<1$ are precisely the elements of $\ker \chi_{0,Q}$; every $A$-section $\chi$ of $\varphi_Q \circ C$ reducing to $\chi_{0,Q}$ is realised by a unique place in $D_Q$; the valuation subring of each $P \in D_Q$ consists of the quotients $g/h$ with $g,h \in S_Q$ and $P(h) \ne 0$; a nonzero element of `fieldBar q M'` of order $0$ at all $P \in D_Q$ becomes a unit of $S_Q$ after multiplication by a nonzero constant of $\overline{\mathbb{Q}}$; and an element of $R.$`integers` integral at all $P \in D_Q$ lies in $S_Q$.
--
--   `hdisj`: for $Q, Q' \notin N$, the sets $D_Q$ and $D_{Q'}$ are disjoint unless $Q = Q'$.
--
--   `hcusp`: for $Q \notin N$ and every $P \in D_Q$, the image in `fieldBar q M'` of the coefficient embedding of `jq` has nonnegative order at $P$.
--
--   `heqv`: for every $\tau$ in the subgroup of $\overline{\mathbb{Q}}$-automorphisms of `fieldBar q M'` generated by the `levelAutBar q M' ζ γ` with $\zeta \in$ `Idx q` and $\gamma \in \Gamma_0(M')$, and every witness $h_\tau$ that $\tau$ preserves $R.$`integers`, the induced residue automorphism `R.resAut τ hτ` of `FSS` over $\kappa$ satisfies: a place $Q$ lies in $N$ if and only if its translate does, and for $Q \notin N$ the translated disc `RegularProlongation.smulDisc τ (Dx Q)` equals $D$ at the translated place.
--
--   `hdl` (the Drinfeld identification, assumed level-equivariantly): for every $\mathbb{F}_{q^2}$-algebra structure on $\kappa$, every proof that [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, and every $\zeta \in$ `Idx q`, there exist a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and an isomorphism $e \colon$ `FSS` $\cong$ [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) of $\kappa$-algebras — the latter being the fixed field inside the Drinfeld function field `FractionRing (CoordRing q κ)` of the subgroup generated by the actions of the elements $(1,\zeta')$, $\zeta' \in C_s$ — such that $\operatorname{card} C_s = 2\cdot$`placeWidthChar q M' s` (twice the width invariant of $s$, the quotient of `jWidthChar q` at $s(\,$`jGeomGen`$\,)$ by `placeRamificationJ`), and such that for every $\gamma \in \Gamma_0(M')$, given a witness that `levelAutBar q M' ζ γ⁻¹` preserves $R.$`integers` and a witness that $($`redQ q γ`$, 1)$ lies in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) (the kernel of the character $(g,u) \mapsto \det(g)\, u^{q+1}$), the automorphism `R.resAut (levelAutBar q M' ζ γ⁻¹)` of `FSS` corresponds under $e$ to the action [`DrinfeldCurve.hFunctionFieldAction`](def/DrinfeldCurve_FunctionField.html#L16) of $($`redQ q γ`$, 1)$ on the Drinfeld function field.
--
--   Conclusion. Under these hypotheses both of the following hold.
--
--   First, the level automorphisms act transitively on $N$: for all places $x, x' \in N$ there exist $\zeta \in$ `Idx q`, an element $\gamma \in \Gamma_0(M')$ and a witness $h_\tau$ that `levelAutBar q M' ζ γ` preserves $R.$`integers`, such that `R.resAut (levelAutBar q M' ζ γ) hτ • x = x'`.
--
--   Second, no place outside $N$ is fixed by all of them: for every place $Q \notin N$ there exist $\zeta \in$ `Idx q`, an element $\gamma \in \Gamma_0(M')$ and a witness $h_\tau$ that `levelAutBar q M' ζ γ` preserves $R.$`integers`, such that `R.resAut (levelAutBar q M' ζ γ) hτ • Q ≠ Q`.
--
--   On the supersingular components of the special fibre at $q$ of the modular curve of level $q^2M'$, the reduced field is the function field of the Drinfeld (Deligne–Lusztig) curve for $SL_2(\mathbb{F}_q)$, and the $q+1$ places in $N$ are its ends, the points where the component meets the rest of the fibre. The statement records the two group-theoretic facts needed about the $\Gamma_0(M')$-action through this identification — transitivity on the ends, and the absence of a place off the ends fixed by the whole level group — and feeds into the determination of level orbits and inertia on the supersingular component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_levelAut_transitive_ends_moves_smoothPlaces.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_levelAut_transitive_ends_moves_smoothPlaces
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

    (hdl : (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                ∀ x : FSS,
                  ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))))) :
        (∀ x x' : Place (ResidueField ↥A) FSS, x ∈ N → x' ∈ N →
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M')
            (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ f ∈ R.integers ↔ f ∈ R.integers),
            R.resAut (levelAutBar q M' ζ γ) hτ • x = x') ∧
        (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M')
            (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ f ∈ R.integers ↔ f ∈ R.integers),
            R.resAut (levelAutBar q M' ζ γ) hτ • Q ≠ Q) := by sorry
