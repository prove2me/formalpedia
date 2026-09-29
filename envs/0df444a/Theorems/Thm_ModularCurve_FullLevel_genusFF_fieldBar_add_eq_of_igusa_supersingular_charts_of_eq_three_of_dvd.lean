-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/dc3cb361-a909-57ec-861c-c29e1e39ce30
-- title:
--   Genus identity for the semistable covering at q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a nonunit, with residue field $\kappa =$ `ResidueField A`, and let $W$ be a finite set of places of `modularFunctionFieldC κ M'` over $\kappa$ whose members are exactly the elements of `ssPlaces q M' κ`, i.e. the rational affine geometric places at which the value of `jGeomGen` lies in `ssJSet q`. Write $\bar F =$ `fieldBar q M'` for the base change to $\overline{\mathbb Q}$ of the function field of $X_H$ of level $q^2M'$, $H$ the kernel of $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$ (units $\equiv 1 \bmod q$), and assume `modularFunctionFieldBar M'` $\le \bar F$. The data are: a constant reduction $R_0$ of `modularFunctionFieldBar M'` along $A$ with values in `modularFunctionFieldC κ M'` whose residue map computes coefficientwise reduction on Laurent series with coefficients in $A$; a primitive $q$-th root of unity $\zeta$; families $O_{\mathrm{Ig}}$ of valuation subrings of $\bar F$ indexed by the points of $\mathbb P^1(\mathbb Z/q)$ and $O_{\mathrm{SS}}$ indexed by $W$; and fields $F_{\mathrm{Ig}}(\ell)$, $F_{\mathrm{SS}}(s)$ over $\kappa$ carrying component charts $C_{\mathrm{Ig}}$, $C_{\mathrm{SS}}$ of $\bar F$ relative to $A$ whose rings of integers are the corresponding $O_{\mathrm{Ig}}$, $O_{\mathrm{SS}}$. The hypotheses on these families, summarised here, are: $O_{\mathrm{Ig}}$ at the point `lineInfty q` consists of those $f$ with $f\cdot \bar y = \bar x$ for Laurent series $x,y$ over $A$ with $y$ reducing to a nonzero series; every point is reached from `lineInfty q` by the mod-$q$ reduction of some $\gamma \in \Gamma_0(M')$, with the corresponding subring the pullback of that at `lineInfty q` along `levelAutBar q M' ζ γ`; $O_{\mathrm{Ig}}$ is injective and the family is permuted by every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; each $O_{\mathrm{SS}}(s)$ meets the constants exactly in $A$, is invariant under every such `levelAutBar q M' ζ' γ`, contains an element $t$ with $t - a$ a unit for all $a \in A$, and specialises to $s$, in the sense that for $f$ in $R_0$'s ring of integers which is regular at every place where `jq` is, if the $R_0$-residue of $f$ lies in the valuation subring of $s$ then the image of $f$ in $\bar F$ lies in $O_{\mathrm{SS}}(s)$ and its difference with any $a \in A$ whose reduction is the value of $s$ at that residue lies in the maximal ideal of $O_{\mathrm{SS}}(s)$. The conclusion is the numerical identity $$\operatorname{genusFF}(\overline{\mathbb Q},\bar F) + \bigl(\#\mathbb P^1(\mathbb Z/q) + \#W\bigr) = \sum_{\ell} \operatorname{genusFF}(\kappa, F_{\mathrm{Ig}}(\ell)) + \sum_{s \in W} \operatorname{genusFF}(\kappa, F_{\mathrm{SS}}(s)) + \#\mathbb P^1(\mathbb Z/q)\cdot \#W + 1,$$ where `genusFF` is the genus of a function field, computed as the dimension of $H^1$ of the zero divisor.
--
--   This is the genus (plumbing) identity for the semistable covering of the modular curve of level $q^2M'$ in the case $q=3$: both sides express the arithmetic genus of a semistable curve whose components are the $q+1$ Igusa charts and the $|W|$ supersingular charts and whose dual graph is the complete bipartite graph on these two sets, so that the genus of the generic fibre equals the sum of the component genera plus the number of edges minus the number of vertices plus one. It feeds the assembly of the semistable covering at $q=3$, where the charts and their intersection data are produced together with this count.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_three_of_dvd
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
    (FIg : CuspidalType.ProjLine q → Type) [∀ ℓ, Field (FIg ℓ)] [∀ ℓ, Algebra (ResidueField A) (FIg ℓ)]
    (FSS : ↥W → Type) [∀ s, Field (FSS s)] [∀ s, Algebra (ResidueField A) (FSS s)]
    (CIg : ∀ ℓ, ComponentChart A (fieldBar q M') (FIg ℓ)) (CSS : ∀ s, ComponentChart A (fieldBar q M') (FSS s))
    (hCIg_int : ∀ ℓ, (CIg ℓ).integers = OIg ℓ) (hCSS_int : ∀ s, (CSS s).integers = OSS s)
    :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') + (Nat.card (CuspidalType.ProjLine q) + W.card) =
    ∑ᶠ ℓ : CuspidalType.ProjLine q, AlgebraicCurve.genusFF (ResidueField A) (FIg ℓ) +
      ∑ s ∈ W.attach, AlgebraicCurve.genusFF (ResidueField A) (FSS s) +
        Nat.card (CuspidalType.ProjLine q) * W.card + 1 := by sorry
