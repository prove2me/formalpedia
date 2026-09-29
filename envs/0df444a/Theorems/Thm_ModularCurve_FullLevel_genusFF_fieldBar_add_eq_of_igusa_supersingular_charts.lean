-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_genusFF_fieldBar_add_eq_of_igusa_supersingular_charts
-- name    : ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/0cc29f91-ab09-59c8-8f1b-f412129efa6e
-- title:
--   Genus identity for the semistable covering of X_H(q²M')
-- statement:
--   Fix a prime $q \ge 5$ and a non-zero natural number $M'$ with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $q$ a non-unit of $A$; write $\kappa =$ `ResidueField A`. Let $W$ be a finset of places of `modularFunctionFieldC κ M'` over $\kappa$ whose members are exactly the supersingular places `ssPlaces q M' κ` (rational affine geometric places at which the generator takes a supersingular $j$-value). Assume `modularFunctionFieldBar M'` $\le$ `fieldBar q M'` inside `LaurentSeries` $\overline{\mathbb{Q}}$, and let $R_0$ be a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` which on Laurent series with coefficients in $A$ is coefficientwise reduction. Fix $\zeta$ in `Idx q`, a family $O_{\mathrm{Ig}}$ of valuation subrings of `fieldBar q M'` indexed by the projective line $\mathbb{P}^1(\mathbb{Z}/q)$ and a family $O_{\mathrm{SS}}$ indexed by $W$, subject to: $O_{\mathrm{Ig}}$ at the point $[1:0]$ consists of the $f$ for which $f \cdot y = x$ for some Laurent series $x,y$ over $A$ with $y$ having non-zero coefficientwise reduction; every $O_{\mathrm{Ig}}(\ell)$ is the pullback of that ring along `levelAutBar q M' ζ γ` for some $\gamma \in \Gamma_0(M')$ inducing $\ell$ from $[1:0]$; $O_{\mathrm{Ig}}$ is injective and is permuted by all `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; each $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb{Q}}$ exactly in $A$, is fixed by all such `levelAutBar q M' ζ' γ`, contains an element $t$ with $t - a$ a unit for every $a \in A$, and receives elements of $R_0$'s valuation ring that are regular where the $j$-generator is, with prescribed residues (these compatibilities are summarised here). Finally let `FIg ℓ` and `FSS s` be fields over $\kappa$ carrying `ComponentChart`s `CIg ℓ`, `CSS s` for $A$ and `fieldBar q M'` whose rings of integers are $O_{\mathrm{Ig}}(\ell)$ and $O_{\mathrm{SS}}(s)$. Then, with `genusFF` the dimension of $H^1$ of the zero divisor,
--   $$\mathrm{genus}_{\overline{\mathbb{Q}}}(\mathtt{fieldBar } q\, M') + \bigl(\#\mathbb{P}^1(\mathbb{Z}/q) + \#W\bigr) = \sum_{\ell} \mathrm{genus}_{\kappa}(\mathtt{FIg } \ell) + \sum_{s \in W} \mathrm{genus}_{\kappa}(\mathtt{FSS } s) + \#\mathbb{P}^1(\mathbb{Z}/q)\cdot \#W + 1.$$
--
--   This is the numerical clause of the semistable covering of the full-level modular curve $X_{\Gamma_H(q^2M')}$ at $q$: the genus of the generic fibre, together with the number of components, is expressed through the genera of the Igusa and Drinfeld (supersingular) components and the number of nodes, the dual graph being the complete bipartite graph on $\mathbb{P}^1(\mathbb{Z}/q)$ and the supersingular places. It feeds the assembly theorem producing the semistable covering together with its equivalence clauses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_genusFF_fieldBar_add_eq_of_igusa_supersingular_charts.lean

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

open IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open ModularCurve
open ModularCurve.FullLevel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts
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
    (FIg : CuspidalType.ProjLine q → Type) [∀ ℓ, Field (FIg ℓ)] [∀ ℓ, Algebra (ResidueField A) (FIg ℓ)]
    (FSS : ↥W → Type) [∀ s, Field (FSS s)] [∀ s, Algebra (ResidueField A) (FSS s)]
    (CIg : ∀ ℓ, ComponentChart A (fieldBar q M') (FIg ℓ)) (CSS : ∀ s, ComponentChart A (fieldBar q M') (FSS s))
    (hCIg_int : ∀ ℓ, (CIg ℓ).integers = OIg ℓ) (hCSS_int : ∀ s, (CSS s).integers = OSS s)
    :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') + (Nat.card (CuspidalType.ProjLine q) + W.card) =
    ∑ᶠ ℓ : CuspidalType.ProjLine q, AlgebraicCurve.genusFF (ResidueField A) (FIg ℓ) +
      ∑ s ∈ W.attach, AlgebraicCurve.genusFF (ResidueField A) (FSS s) +
        Nat.card (CuspidalType.ProjLine q) * W.card + 1 := by sorry
