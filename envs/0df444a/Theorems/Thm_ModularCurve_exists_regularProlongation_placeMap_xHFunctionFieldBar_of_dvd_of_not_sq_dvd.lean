-- Prove2me | Theorems.Thm_ModularCurve_exists_regularProlongation_placeMap_xHFunctionFieldBar_of_dvd_of_not_sq_dvd
-- name    : ModularCurve.exists_regularProlongation_placeMap_xHFunctionFieldBar_of_dvd_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/a554cb6a-d580-532b-af7b-26c21e43ca70
-- title:
--   Reduction of divisors of X_H(M) at p ‖ M
-- statement:
--   Let $p$ be prime and $M$ a nonzero natural number with $p \mid M$ but $p^2 \nmid M$, and let $H \le (\mathbf{Z}/M)^\times$ contain every unit that maps to $1$ under the reduction $(\mathbf{Z}/M)^\times \to (\mathbf{Z}/(M/p))^\times$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$. Write $F$ for `xHFunctionFieldBar M H`, the $\overline{\mathbf{Q}}$-base change inside $\overline{\mathbf{Q}}((q))$ of the level-$\Gamma_H(M)$ function field, $\bar F_M$ for the $q$-expansion field `qExpFunctionFieldC` over $\kappa$ at level `GammaH M H`, and $\bar F'$ for the one at level `GammaH (M/p) (infSubgroup p M H hpM)`, where `infSubgroup` is the image of $H$ in $(\mathbf{Z}/(M/p))^\times$. The assertion is that there exist a regular prolongation $R$ of $A$ to $F$ with residue field $\bar F_M$ — that is, a valuation subring $R.\mathrm{integers}$ of $F$ meeting $\overline{\mathbf{Q}}$ exactly in $A$, together with a surjective ring map onto $\bar F_M$ with kernel the maximal ideal and compatible with reduction on $A$ — and a map $r$ from places of $F/\overline{\mathbf{Q}}$ to places of $\bar F'/\kappa$, such that: (i) for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbf{Q}}((q))$ lies in $F$, that element is $R$-integral and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$; and (ii) for every $R$-integral $f$ with nonzero residue, every $g \in \bar F'$ having the same Laurent expansion as that residue, and every divisor $D$ on the places of $F$ with $D(P) = \mathrm{ord}_P(f)$ for all $P$ (orders being $-\log$ of the adic valuation), there is a divisor $E$ on the places of $\bar F'$ supported on the supersingular set `ssPlacesQExp` at $p$ with $(\mathrm{mapDomain}\,r\,D)(Q) + E(Q) = \mathrm{ord}_Q(g)$ for all $Q$.
--
--   This is the Deuring-style reduction of divisors along the Gauss (i.e. $\infty$-branch) prolongation of a place $A \mid p$ of $\overline{\mathbf{Q}}$: off the supersingular places, the divisor of a function on $X_H(M)_{\overline{\mathbf{Q}}}$ specialises place by place to the divisor of its reduction read on the component of the special fibre through $\infty$, which is the modular curve of level $\Gamma_{H'}(M/p)$, the discrepancy $E$ being supported on supersingular places and not computed explicitly. It feeds the construction of reduced root functions and the torsion computations on the Jacobian used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_regularProlongation_placeMap_xHFunctionFieldBar_of_dvd_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_regularProlongation_placeMap_xHFunctionFieldBar_of_dvd_of_not_sq_dvd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] :
    ∃ (R : AlgebraicCurve.RegularProlongation A ↥(ModularCurve.xHFunctionFieldBar M H) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH M H)))
      (r : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) →
        AlgebraicCurve.Place (IsLocalRing.ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      (∀ (y : LaurentSeries ↥A) (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.xHFunctionFieldBar M H),
        ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ : ↥(ModularCurve.xHFunctionFieldBar M H)) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
            ModularCurve.coeffMap (IsLocalRing.residue ↥A) y) ∧
      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ g : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
          (g : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
            ((R.residue f : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) →
          ∀ D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
            (∀ P, D P = P.ord (f : ↥(ModularCurve.xHFunctionFieldBar M H))) →
            ∃ E : AlgebraicCurve.Divisor (IsLocalRing.ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
              (∀ Q, E Q ≠ 0 → Q ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥A)
                (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) ∧
              ∀ Q, Finsupp.mapDomain r D Q + E Q = Q.ord g) := by sorry
