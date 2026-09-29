-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/ebd5b547-6478-5094-87b1-29a9a4219025
-- title:
--   Fixed charted type II points contain the supersingular affinoid, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number not divisible by $q$, and let $\ell$ be a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, with residue field $\kappa =$ `ResidueField A`. Let $W$ be a finite set of places of $\kappa$-curve `modularFunctionFieldC` $\kappa\,M'$ whose members are exactly the elements of `ssPlaces q M' κ`, i.e. the rational, affine geometric places whose value at `jGeomGen` is a supersingular $j$-invariant, and let $s \in W$. Assume `modularFunctionFieldBar M'` $\le$ `fieldBar q M'` via `hle`. Let $R_0$ be a constant reduction of the base-changed full-level field `modularFunctionFieldBar M'` along $A$ with values in `modularFunctionFieldC κ M'` (a valuation subring `integers` prolonging $A$, a surjective residue map with kernel the maximal ideal, compatible with $A$ on constants, together with a map on places preserving degrees and orders), subject to `hR₀`: every Laurent series $y$ over $A$ whose coefficientwise image lies in `modularFunctionFieldBar M'` lies in $R_0$.`integers`, and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Let $F_{ss}$ be a field over $\kappa$, let $C$ be a component chart of `fieldBar q M'` along $A$ with reduction field $F_{ss}$, and let `An : E → Annulus A (fieldBar q M')` be a family of annuli. Call a component chart $C_o$ of `fieldBar q M'` along $A$ *centred at $s$* when, for every $f \in R_0$.`integers` having nonnegative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ where the $q$-expansion `jq` of $j$ has nonnegative order, and whose $R_0$-residue lies in the valuation ring of $s$: the image of $f$ in `fieldBar q M'` lies in $C_o$.`integers`, and for each $a \in A$ whose residue equals the value at $s$ of that $R_0$-residue, $f - a$ lies in the maximal ideal of $C_o$.`integers`. Write $R_D$, for a set $D$ of places, for the set of $f \in$ `fieldBar q M'` lying in the valuation ring of every $P \in D$ and with $P.\mathrm{evalAt}\,f \in A$. Assume: (`hexh`) for every field $F_o$ which is a curve over $\kappa$ and essentially of finite type over $\kappa$, every component chart $C_o$ with reduction field $F_o$ that is centred at $s$ satisfies $R_{C.\mathrm{dom}} \subseteq C_o$.`integers` or $R_{(\mathrm{An}\,e).\mathrm{dom}} \subseteq C_o$.`integers` for some $e \in E$; (`hmove`) for each $e$ there are $\zeta \in$ `Idx q` and $\gamma \in \Gamma_0(M')$ with $((\mathrm{An}\,e).\mathrm{comap}\,(\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma)).\mathrm{dom} = (\mathrm{An}\,e').\mathrm{dom}$ for some $e' \neq e$; (`hsep`) any valuation subring $O$ of `fieldBar q M'` that prolongs $A$, contains an element $t$ with $t-a$ a unit of $O$ for every $a \in A$, does not contain $R_{C.\mathrm{dom}}$, and contains both $R_{(\mathrm{An}\,e).\mathrm{dom}}$ and $R_{(\mathrm{An}\,e').\mathrm{dom}}$, forces $e = e'$. The conclusion is that for every field $F_o$ that is a curve over $\kappa$ and essentially of finite type over $\kappa$ and every component chart $C_o$ of `fieldBar q M'` along $A$ with reduction field $F_o$ which is centred at $s$ and whose ring of integers is invariant under pullback along `levelAutBar q M' ζ γ` for all $\zeta$ and all $\gamma \in \Gamma_0(M')$, one has $R_{C.\mathrm{dom}} \subseteq C_o$.`integers`.
--
--   This is the $q=3$ instance of the statement that a type II point of the full-level modular curve lying over a supersingular place and fixed by all level automorphisms must sit at the centre of the supersingular affinoid rather than on one of the node annuli; the auxiliary level condition $\ell \mid M'$ with $\ell \equiv 11 \pmod{12}$ rigidifies the extra automorphisms of the supersingular curve in characteristic $3$. It feeds the identification of the chart of integers attached to such a component, [`ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_three_of_dvd), in the analysis of the semistable reduction of the full-level curve at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.forall_tubeBounded_mem_of_fixed_of_typeII_exhaustion_charted_of_eq_three_of_dvd
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
    (s : ↥W)
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (C : ComponentChart A (fieldBar q M') FSS)
    {E : Type} (An : E → Annulus A ↥(fieldBar q M'))

    (hexh : ∀ (Fo : Type) (_ : Field Fo) (_ : Algebra (ResidueField A) Fo)
        (_ : IsCurveOver (ResidueField A) Fo) (_ : Algebra.EssFiniteType (ResidueField A) Fo)
        (Co : ComponentChart A (fieldBar q M') Fo),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          (IntermediateField.inclusion hle f : fieldBar q M') ∈ Co.integers ∧
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
                - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ Co.integers,
              (⟨_, h⟩ : Co.integers) ∈ maximalIdeal Co.integers) →
        (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ Co.integers) ∨ ∃ e : E, (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An e).dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ Co.integers))

    (hmove : ∀ e : E, ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ ∃ e' : E, e' ≠ e ∧
        ((An e).comap (levelAutBar q M' ζ γ)).dom = (An e').dom)

    (hsep : ∀ (O : ValuationSubring ↥(fieldBar q M')) (e e' : E),
        (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A) →
        (∃ t : ↥(fieldBar q M'), t ∈ O ∧ ∀ a : A,
          ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O, IsUnit (⟨_, h⟩ : O)) →
        ¬ (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) →
        (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An e).dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) →
        (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An e').dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) → e = e') :
    ∀ (Fo : Type) (_ : Field Fo) (_ : Algebra (ResidueField A) Fo)
      (_ : IsCurveOver (ResidueField A) Fo) (_ : Algebra.EssFiniteType (ResidueField A) Fo)
      (Co : ComponentChart A (fieldBar q M') Fo),
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          (IntermediateField.inclusion hle f : fieldBar q M') ∈ Co.integers ∧
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
                - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ Co.integers,
              (⟨_, h⟩ : Co.integers) ∈ maximalIdeal Co.integers) →
      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → Co.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = Co.integers) →
      (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ Co.integers) := by sorry
