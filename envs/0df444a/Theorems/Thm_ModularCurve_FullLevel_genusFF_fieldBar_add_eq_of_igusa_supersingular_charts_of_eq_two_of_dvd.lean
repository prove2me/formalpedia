-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/fe0507f0-41a6-58a2-aebc-a14c4cf02902
-- title:
--   Genus identity for the semistable covering at q=2
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $\ell$ be a prime with $\ell \equiv 11 \pmod{12}$ dividing $M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ in which $q$ is a non-unit, write $\kappa$ for its residue field, and let $W$ be a finite set of places of `modularFunctionFieldC κ M'` over $\kappa$ whose members are exactly the supersingular places `ssPlaces q M' κ`, i.e. the rational affine geometric places at which the geometric $j$-generator takes a supersingular value. Assume `modularFunctionFieldBar M'` (the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field) is contained in `fieldBar q M'` (the base change of the function field of level $\Gamma_H(q^2M')$), and let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` along $A$ with residue field `modularFunctionFieldC κ M'`: a valuation subring of the former lying over $A$, a surjective residue homomorphism with kernel the maximal ideal extending the residue map of $A$, a degree-preserving map on places compatible with divisors of functions, and the normalisation that on Laurent series with coefficients in $A$ the residue is coefficientwise reduction. Fix a primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$, and families of valuation subrings $O_{\mathrm{Ig}}$ of `fieldBar q M'` indexed by $\mathbb{P}^1(\mathbb{Z}/q)$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to two groups of hypotheses, summarised here: the Igusa clauses (the ring at the line at infinity consists of those $f$ admitting Laurent series $x, y$ over $A$ with $y$ of nonzero reduction and $f \cdot y = x$; the whole family is the orbit of that ring under the comaps of the automorphisms `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$, acting transitively on the index set, the indexing being injective, and each such comap, for any choice of root of unity, permuting the family), and the supersingular clauses (each $O_{\mathrm{SS}}(s)$ lies over $A$, is fixed by all these comaps, contains an element $t$ such that $t - a$ is a unit for every $a \in A$, and reduces compatibly with $R_0$ and $s$: any $f$ in the integers of $R_0$ which is regular at every place where the image of $jq$ is regular and whose $R_0$-residue lies in the valuation ring of $s$ belongs to $O_{\mathrm{SS}}(s)$, with $f - a$ in the maximal ideal whenever the residue of $a \in A$ equals the value of $R_0$'s residue of $f$ at $s$). Finally let $F_{\mathrm{Ig}}(\ell')$, for $\ell' \in \mathbb{P}^1(\mathbb{Z}/q)$, and $F_{\mathrm{SS}}(s)$, for $s \in W$, be fields over $\kappa$ carrying component charts for $A$ on `fieldBar q M'` whose rings of integers are $O_{\mathrm{Ig}}(\ell')$ and $O_{\mathrm{SS}}(s)$ respectively. Then
--   $$g\big(\mathrm{fieldBar}\, q\, M'/\overline{\mathbb{Q}}\big) + \big(\#\mathbb{P}^1(\mathbb{Z}/q) + \#W\big) = \sum_{\ell'} g\big(F_{\mathrm{Ig}}(\ell')/\kappa\big) + \sum_{s \in W} g\big(F_{\mathrm{SS}}(s)/\kappa\big) + \#\mathbb{P}^1(\mathbb{Z}/q)\cdot\#W + 1,$$
--   where $g$ denotes [`AlgebraicCurve.genusFF`](def/AlgebraicCurve_Repartitions.html#L145), the $\kappa$- (resp. $\overline{\mathbb{Q}}$-) dimension of the first cohomology of the zero divisor.
--
--   This is the genus bookkeeping of the semistable covering of the full-level modular curve at the prime $q = 2$: the total genus plus the number of vertices of the dual graph equals the sum of the genera of the components plus the number of edges plus one, the dual graph being the complete bipartite graph on the $q+1$ Igusa components and the $\#W$ supersingular (Drinfeld) components. It is cited by the assembly of the semistable covering from the Igusa and supersingular valuation subrings and their charts, where it supplies the genus clause; the component genera themselves are computed by the Igusa and Drinfeld genus lemmas, with the supersingular count coming from the Eichler mass formula in the form $12\,\#W = \psi(M')$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_two_of_dvd.lean

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
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_EichlerMass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_two_of_dvd
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
    (FIg : CuspidalType.ProjLine q → Type) [∀ ℓ, Field (FIg ℓ)] [∀ ℓ, Algebra (ResidueField A) (FIg ℓ)]
    (FSS : ↥W → Type) [∀ s, Field (FSS s)] [∀ s, Algebra (ResidueField A) (FSS s)]
    (CIg : ∀ ℓ, ComponentChart A (fieldBar q M') (FIg ℓ)) (CSS : ∀ s, ComponentChart A (fieldBar q M') (FSS s))
    (hCIg_int : ∀ ℓ, (CIg ℓ).integers = OIg ℓ) (hCSS_int : ∀ s, (CSS s).integers = OSS s)
    :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') + (Nat.card (CuspidalType.ProjLine q) + W.card) =
    ∑ᶠ ℓ : CuspidalType.ProjLine q, AlgebraicCurve.genusFF (ResidueField A) (FIg ℓ) +
      ∑ s ∈ W.attach, AlgebraicCurve.genusFF (ResidueField A) (FSS s) +
        Nat.card (CuspidalType.ProjLine q) * W.card + 1 := by sorry
