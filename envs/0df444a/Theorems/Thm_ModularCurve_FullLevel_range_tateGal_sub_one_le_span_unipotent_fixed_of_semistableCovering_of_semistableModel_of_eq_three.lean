-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_range_tateGal_sub_one_le_span_unipotent_fixed_of_semistableCovering_of_semistableModel_of_eq_three
-- name    : ModularCurve.FullLevel.range_tateGal_sub_one_le_span_unipotent_fixed_of_semistableCovering_of_semistableModel_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/1bf5e67b-b0df-5158-8018-512038e24fcb
-- title:
--   Inertia image spanned by unipotent-fixed translates, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\lambda$ be a prime different from $q$. Assume `LevelAutInputs q M'` (for every primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$ and every $\gamma \in \Gamma_0(M')$ there is an $\overline{\mathbb{Q}}$-algebra automorphism of `fieldBar q M'` satisfying `IsLevelAutBar`) and `GL2Laws q M'` (a monoid homomorphism from $GL_2(\mathbb{Z}/q)$ to the additive endomorphisms of `Jac q M'` agreeing with `slJac` on the reductions of $\Gamma_0(M')$ and with `diagJac` on the elements `diagOneElem`). Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, let $W$ be the finite set of places of `modularFunctionFieldC (ResidueField P) M'` over the residue field consisting exactly of the supersingular places `ssPlaces q M'`, let $\pi \in P$ satisfy $\pi^{q^2-1} = q$, let $\iota$ be a ring homomorphism from $\mathbb{F}_{q^2}$ to the residue field of $P$, with [`DrinfeldCurve.CoordRing q (ResidueField P)`](def/DrinfeldCurve_CoordRing.html#L21) a domain, let `hle` witness `modularFunctionFieldBar M' ≤ fieldBar q M'`, and let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` along $P$ with values in `modularFunctionFieldC (ResidueField P) M'` whose integers contain every coefficientwise image of a Laurent series over $P$ lying in `modularFunctionFieldBar M'`, with $R_0$-residue the coefficientwise reduction of that series. Regard the residue field of $P$ as an $\mathbb{F}_{q^2}$-algebra via $\iota$. Then for every semistable covering $\mathcal{C}$ of `fieldBar q M'` over $P$ with supersingular set $W$ satisfying the equivalence clauses, the hedged Drinfeld clause (for each index $\zeta$ and each $s \in W$ there is $\eta \in \{1,q\}$ with `𝒞.DrinfeldClause π ι η ζ s`), the Igusa unipotent clause for every $\zeta$, the level-pinning clauses for `hle` and $R_0$, the inertia clause at $\pi$, the width clause at $\pi$, and the genus, discrete-fibre, curve and naturality clauses, for every semistable model $M$ of `fieldBar q M'` over $P$ with component fields and charts the sum data of $\mathcal{C}$, annuli $\mathcal{C}.\mathrm{An}\,\ell\,s$, sources `Sum.inl`, targets `Sum.inr` and node places the corresponding `sumNode`, for every descent $D$ of $M$, and for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ with `tameCharacter π τ = 1`, the range of `(tateGal q M' lam τ).baseChange ℚ_[lam] - 1` on $\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda(\mathrm{Jac}(q;M'))$ is contained in the $\mathbb{Q}_\lambda$-span of those $x$ of the form $x = g \cdot v$ with $g \in GL_2(\mathbb{Z}/q)$ acting through `tateGL2` and $v$ fixed by `tateGL2` of every unipotent matrix `unipotent q t`, $t \in \mathbb{Z}/q$.
--
--   This is the Picard–Lefschetz (vanishing-cycle) input at the prime $q$ in the form needed for level lowering: the toric part of the $\lambda$-adic Tate module of the full-level Jacobian, measured by $\tau - 1$ for tame-trivial inertia, is accounted for by $GL_2(\mathbb{F}_q)$-translates of vectors fixed by the upper unipotent subgroup. It is the $q=3$ case, in which the clause census of the semistable covering carries the Drinfeld clause with the inertia exponent hedged chart by chart, and it feeds [`ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_reduction_of_inertiaIgusa_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_range_tateGal_sub_one_le_span_unipotent_fixed_of_semistableCovering_of_semistableModel_of_eq_three.lean

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

theorem ModularCurve.FullLevel.range_tateGal_sub_one_le_span_unipotent_fixed_of_semistableCovering_of_semistableModel_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
