-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_range_tateGal_sub_one_le_span_unipotent_fixed_of_semistableCovering_of_semistableModel_of_eq_two
-- name    : ModularCurve.FullLevel.range_tateGal_sub_one_le_span_unipotent_fixed_of_semistableCovering_of_semistableModel_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/de7d8f88-f41b-5753-ad51-31023838bb93
-- title:
--   Unipotent-fixed GL₂(𝔽_q)-translates span (τ-1)V at q=2
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\lambda$ be a prime with $\lambda \neq q$. Assume the level-automorphism inputs `LevelAutInputs q M'` (for each $\zeta$ in `Idx q` and each $\gamma \in \Gamma_0(M')$ an automorphism of `fieldBar q M'` satisfying `IsLevelAutBar`) and the laws `GL2Laws q M'` (a monoid homomorphism from $\mathrm{GL}_2(\mathbb{Z}/q)$ to $\mathrm{End}(\operatorname{Jac} q\,M')$ inducing `slJac` on reductions of $\Gamma_0(M')$ and `diagJac` on diagonal elements). Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, let $W$ be the finite set of supersingular places of `modularFunctionFieldC (ResidueField P) M'`, let $\pi \in P$ satisfy $\pi^{q^2-1} = q$, and let $\iota : \mathbb{F}_{q^2} \to \operatorname{ResidueField} P$ be a ring homomorphism, the residue field being viewed as an $\mathbb{F}_{q^2}$-algebra through $\iota$, with [`DrinfeldCurve.CoordRing q (ResidueField P)`](def/DrinfeldCurve_CoordRing.html#L21) a domain. Let `hle` witness that `modularFunctionFieldBar M'` is contained in `fieldBar q M'`, and let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField P) M'` along $P$ which is compatible with coefficientwise reduction of Laurent series: for every Laurent series $y$ over $P$ whose image under `coeffMap P.subtype` lies in `modularFunctionFieldBar M'`, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\operatorname{ResidueField} P$, is the coefficientwise residue of $y$. Then for every semistable covering $\mathcal{C}$ of type `SemistableCovering q M' P W` satisfying: the equivariance clauses, for every index $\zeta$ and every $s \in W$ a Drinfeld clause `DrinfeldClause π ι η ζ s` with some exponent $\eta \in \{1, q\}$, the Igusa unipotent clause for every $\zeta$, the level-pinning clauses relative to `hle` and $R_0$, the inertia clause at $\pi$, the width clause at $\pi$, and the genus, disc-fibre, curve and naturality clauses; and for every semistable model $M$ of `fieldBar q M'` over $P$ built from the telescoped component charts `sumFbar`, `sumChart`, the annuli $\mathcal{C}.\mathrm{An}$ indexed by pairs in $\mathbb{P}^1(\mathbb{F}_q) \times W$ with the indicated source, target and node maps, and every descent $D$ of $M$: for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ with $P$-tame character $\pi$-value $1$, the image of $(\tau - 1)$ acting on the rational Tate module $\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda(\operatorname{Jac} q\,M')$ through the base change of `tateGal q M' lam τ` is contained in the $\mathbb{Q}_\lambda$-span of those $x$ of the form $g\,v$, where $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ acts through the base change of `tateGL2` and $v$ is fixed by the base-changed action of every unipotent matrix $\begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$, $t \in \mathbb{Z}/q$.
--
--   This is the Picard–Lefschetz step for the full-level modular curve in the case $q = 2$: the toric (vanishing-cycle) part of the $\lambda$-adic Tate module of the Jacobian is captured by $\mathrm{GL}_2(\mathbb{F}_q)$-translates of vectors fixed by the unipotent upper-triangular subgroup, in the form of an inclusion for the image of $\tau - 1$ for tame-trivial inertia. Here the hypothesis on the covering is a per-point Drinfeld clause with hedged exponent $\eta \in \{1, q\}$ together with the Igusa unipotent clause, and the result feeds the construction of the comparison map in [`ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_range_tateGal_sub_one_le_span_unipotent_fixed_of_semistableCovering_of_semistableModel_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.range_tateGal_sub_one_le_span_unipotent_fixed_of_semistableCovering_of_semistableModel_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam)
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (W : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField P)
      (modularFunctionFieldC (IsLocalRing.ResidueField P) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ModularCurve.ssPlaces q M' (IsLocalRing.ResidueField P))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ P)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    [IsDomain (DrinfeldCurve.CoordRing q (IsLocalRing.ResidueField P))]
    (hle : ModularCurve.modularFunctionFieldBar M' ≤ ModularCurve.FullLevel.fieldBar q M')
    (R₀ : AlgebraicCurve.ConstantReduction P ↥(ModularCurve.modularFunctionFieldBar M')
      (modularFunctionFieldC (IsLocalRing.ResidueField P) M'))

    (hR₀ : ∀ (y : LaurentSeries ↥P) (hy : ModularCurve.coeffMap P.subtype y ∈ ModularCurve.modularFunctionFieldBar M'),
      ∃ h : (⟨ModularCurve.coeffMap P.subtype y, hy⟩ : ↥(ModularCurve.modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (IsLocalRing.ResidueField P) M') :
            LaurentSeries (IsLocalRing.ResidueField P)) =
          ModularCurve.coeffMap (IsLocalRing.residue ↥P) y) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField P) := ι.toAlgebra
    ∀ 𝒞 : ModularCurve.FullLevel.SemistableCovering q M' P W,
      𝒞.EquivClauses →
      (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s) →
      (∀ ζ : ModularCurve.FullLevel.Idx q, 𝒞.IgusaUnipotentClause ζ) → 𝒞.LevelPinClauses hle R₀ → 𝒞.InertiaClause π →
      𝒞.WidthClause ⟨π, hπP⟩ → 𝒞.GenusClause → 𝒞.DiscFibreClause → 𝒞.CurveClause → 𝒞.NaturalityClauses →
      ∀ (M : AlgebraicCurve.SemistableModel P ↥(ModularCurve.FullLevel.fieldBar q M') 𝒞.sumFbar 𝒞.sumChart
          (fun e : CuspidalType.ProjLine q × ↥W => 𝒞.An e.1 e.2)
          (fun e => Sum.inl e.1) (fun e => Sum.inr e.2)
          (fun e => 𝒞.sumNode (Sum.inl e.1) e) (fun e => 𝒞.sumNode (Sum.inr e.2) e))
        (D : M.Descent),
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 →
        LinearMap.range ((ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] - 1) ≤
          Submodule.span ℚ_[lam] {x : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') |
            ∃ (g : CuspidalType.GL2 q) (v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M')),
              (∀ t : ZMod q,
                (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] v = v) ∧
              (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam] v = x} := by sorry
