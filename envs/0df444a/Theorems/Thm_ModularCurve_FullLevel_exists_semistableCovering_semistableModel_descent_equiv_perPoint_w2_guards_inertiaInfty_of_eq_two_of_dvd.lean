-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_semistableCovering_semistableModel_descent_equiv_perPoint_w2_guards_inertiaInfty_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_semistableCovering_semistableModel_descent_equiv_perPoint_w2_guards_inertiaInfty_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/54a19928-9ff2-5baf-8051-99a40c6e36f4
-- title:
--   Semistable covering, model and descent at q=2, per-point clauses
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $\ell$ be a prime with $\ell\equiv 11 \pmod{12}$ dividing $M'$. Assume `LevelAutInputs q M'`: for every $\zeta$ in `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb Q}$) and every $\gamma\in\Gamma_0(M')\subseteq \mathrm{SL}_2(\mathbb Z)$ there is an automorphism of `fieldBar q M'` over $\overline{\mathbb Q}$ satisfying `IsLevelAutBar`. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $P$, residue field $\kappa$, let $W$ be a finite set of places of `modularFunctionFieldC κ M'` over $\kappa$ consisting of exactly the members of `ssPlaces q M' κ`, let $\pi\in P$ satisfy $\pi^{q^2-1}=q$, let $\iota:\mathbb F_{q^2}\to\kappa$ be a ring homomorphism, and assume [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain. Let `modularFunctionFieldBar M'` be contained in `fieldBar q M'`, and let $R_0$ be a constant reduction of $P$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` (a valuation subring of the source with surjective residue map onto the target whose kernel is the maximal ideal, compatible with $P$, together with a degree- and order-preserving map of places), subject to $h_{R_0}$: every Laurent series over $P$ whose coefficientwise image lies in `modularFunctionFieldBar M'` lies in $R_0$'s integers and has $R_0$-residue the coefficientwise reduction of that series. Then, with $\kappa$ an $\mathbb F_{q^2}$-algebra via $\iota$, there exist a semistable covering $\mathcal C$ of `fieldBar q M'` along $P$ with vertex set $\mathbb P^1(\mathbb F_q)\sqcup W$ and edges $\mathbb P^1(\mathbb F_q)\times W$ (Igusa charts `CIg`, supersingular charts `CSS`, annuli `An`, `An'`), a semistable model $M$ over $P$ of `fieldBar q M'` for the sum-indexed data `𝒞.sumFbar`, `𝒞.sumChart`, with the annulus of an edge $(\ell_0,s)$ attached at `𝒞.sumNode` to the Igusa source `inl ℓ₀` and the supersingular target `inr s`, and a descent datum $D$ for $M$ (a noetherian henselian local ring with a local injection into $P$, an algebraic subfield of $\overline{\mathbb Q}$, a proper flat model over it of finite presentation whose base change is $M.X$, and a subfield of `fieldBar q M'` over which it is algebraic, matching function fields), such that $\mathcal C$ satisfies: `EquivClauses` (the level automorphisms permute the Igusa charts and fix the supersingular charts, matching annulus domains and moduli); for every $\zeta$ and every $s\in W$ some $\eta\in\{1,q\}$ with `DrinfeldClause π ι η ζ s` (the supersingular component is a quotient of the Drinfeld curve function field by a subgroup of $\mu_{q+1}(\mathbb F_{q^2})$, equivariantly for $\Gamma_0(M')$ through `redQ` and for inertia through the tame character, twisted by $\eta$); `IgusaUnipotentClause ζ` for every $\zeta$ (level automorphisms of unipotent reduction induce the identity on the chart at `lineInfty`); `LevelPinClauses hle R₀` (pinning the charts' residues to $R_0$); `InertiaClause π` (inertia with trivial tame character acts trivially on all charts and annulus parameters); `WidthClause ⟨π, hπP⟩` (each annulus modulus is a unit times $\pi^w$, $w\ge 1$); `GenusClause` (the genus identity for the configuration); `DiscFibreClause`; `CurveClause` (each component field is a curve over $\kappa$, essentially of finite type); `NaturalityClauses`; and `InertiaIgusaInftyClause` (inertia preserves the chart at `lineInfty` and induces the identity on it).
--
--   This is the stable-reduction input for the modular curve of full level $q$ over $\Gamma_0(M')$ at a place above $q=2$: the Igusa components indexed by $\mathbb P^1(\mathbb F_q)$ and the supersingular Drinfeld components indexed by the supersingular places at level $M'$, joined in a complete bipartite pattern of annuli, together with a model over the valuation ring and a descent of that model to a noetherian henselian local ring. It is used to produce the Tate-parameter data in [`FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two_of_dvd`](thm.html#FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two_of_dvd), the per-point form of the clause census being what the later Galois-module computation consumes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_semistableCovering_semistableModel_descent_equiv_perPoint_w2_guards_inertiaInfty_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringInertiaIgusa

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_semistableCovering_semistableModel_descent_equiv_perPoint_w2_guards_inertiaInfty_of_eq_two_of_dvd
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M')
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
    ∃ (𝒞 : ModularCurve.FullLevel.SemistableCovering q M' P W),
      ∃ (M : AlgebraicCurve.SemistableModel P ↥(ModularCurve.FullLevel.fieldBar q M') 𝒞.sumFbar 𝒞.sumChart
          (fun e : CuspidalType.ProjLine q × ↥W => 𝒞.An e.1 e.2)
          (fun e => Sum.inl e.1) (fun e => Sum.inr e.2)
          (fun e => 𝒞.sumNode (Sum.inl e.1) e) (fun e => 𝒞.sumNode (Sum.inr e.2) e))
        (D : M.Descent),
      𝒞.EquivClauses ∧
      (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s) ∧
      (∀ ζ : ModularCurve.FullLevel.Idx q, 𝒞.IgusaUnipotentClause ζ) ∧ 𝒞.LevelPinClauses hle R₀ ∧ 𝒞.InertiaClause π ∧
        𝒞.WidthClause ⟨π, hπP⟩ ∧ 𝒞.GenusClause ∧ 𝒞.DiscFibreClause ∧ 𝒞.CurveClause ∧ 𝒞.NaturalityClauses ∧
        𝒞.InertiaIgusaInftyClause := by sorry
