-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_drinfeldClause_of_valuationSubring_over_fixed_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.SemistableCovering.drinfeldClause_of_valuationSubring_over_fixed_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/25c2a4d1-1aa3-5bf4-9676-a43ac30b033b
-- title:
--   Drinfeld clause at q=3 from supersingular chart valuation rings
-- statement:
--   Fix a prime $q$ with $q = 3$, a nonzero level $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, write $\kappa =$ `ResidueField A`, and let $W$ be a finite set of places of `modularFunctionFieldC` $\kappa\, M'$ over $\kappa$ whose members are exactly the supersingular places (rational, affine geometric, with value of the geometric $j$-invariant in the supersingular set). Assume `modularFunctionFieldBar M'` $\le$ `fieldBar q M'` inside the Laurent series over $\overline{\mathbb{Q}}$, and let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` along $A$ with residue field `modularFunctionFieldC` $\kappa\, M'$, compatible with coefficientwise reduction of Laurent series with coefficients in $A$. For each $s \in W$ let $O_s =$ `OSS s` be a valuation subring of `fieldBar q M'` such that: the preimage of $O_s$ in $\overline{\mathbb{Q}}$ is $A$; for every $f$ in the integers of $R_0$ whose order is nonnegative at every place where that of $j$ is, if the $R_0$-residue of $f$ lies in the valuation ring of $s$ then $f$ lies in $O_s$ and, for each $a \in A$ whose residue equals the value of the residue of $f$ at $s$, the element $f - a$ lies in the maximal ideal of $O_s$; $O_s$ is invariant under `levelAutBar q M' ζ' γ` for every index $\zeta'$ and every $\gamma \in \Gamma_0(M')$; and there is $t \in O_s$ with $t - a$ a unit of $O_s$ for all $a \in A$. Let $\pi \in A$ satisfy $\pi^{q^2-1} = q$, let $\iota : \mathbb{F}_{q^2} \to \kappa$ be a ring homomorphism making `CoordRing q` $\kappa$ a domain, and let $\mathcal{C}$ be a semistable covering of type `SemistableCovering q M' A W` whose supersingular chart at each $s$ has integers exactly $O_s$. Then, viewing $\kappa$ as an $\mathbb{F}_{q^2}$-algebra via $\iota$, for every index $\zeta$ (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $s \in W$ there is $\eta$ with $\eta = 1$ or $\eta = q$ such that `𝒞.DrinfeldClause π ι η ζ s` holds: there are a subgroup $C \le \mu_{q+1}(\mathbb{F}_{q^2})$ and a $\kappa$-algebra isomorphism $e$ from the residue field $\mathcal{C}.\mathrm{FSS}\,s$ of the chart onto the $C$-fixed subfield of the Drinfeld function field over $\kappa$, such that for $\gamma \in \Gamma_0(M')$ the level automorphism attached to $(\zeta,\gamma^{-1})$ induces a ring automorphism of $\mathcal{C}.\mathrm{FSS}\,s$ on that chart, and every automorphism it induces corresponds under $e$ to the action of $(\gamma \bmod q, 1)$; and for every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ and every $\alpha \in \mathbb{F}_{q^2}^{\times}$ with $\iota(\alpha)$ the tame character value of $\tau$ at $\pi$, the arithmetic Galois semilinear automorphism of $\tau$ induces an automorphism on the chart, and every automorphism it induces corresponds under $e$ to the action of $(\mathrm{diag}(1, d^{\eta})^{-1}, \alpha^{\eta})$ for each $d \in (\mathbb{Z}/q)^{\times}$ with image $\alpha^{q+1}$ in $\mathbb{F}_{q^2}$.
--
--   This is the $q = 3$ instance of the identification of the supersingular components in a semistable model of the modular curve of level $q^2M'$ with quotients of the Drinfeld curve $xy^q - x^qy = 1$, together with the prescribed actions of $\Gamma_0(M')$ and of tame inertia; the auxiliary prime $\ell \equiv 11 \pmod{12}$ dividing $M'$ rigidifies the level, which is needed in characteristic $3$ because of the extra automorphisms of the supersingular curve with $j = 0 = 1728$. It feeds the naturality statement for inertia on supersingular charts and the assembly of the W2 clauses for the covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_drinfeldClause_of_valuationSubring_over_fixed_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.drinfeldClause_of_valuationSubring_over_fixed_of_eq_three_of_dvd
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
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

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
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField A)
    [IsDomain (DrinfeldCurve.CoordRing q (IsLocalRing.ResidueField A))]
    (𝒞 : SemistableCovering q M' A W)
    (hCSS : ∀ s, (𝒞.CSS s).integers = OSS s) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField A) := ι.toAlgebra
    ∀ (ζ : Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s := by sorry
