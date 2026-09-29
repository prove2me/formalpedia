-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_fieldBar_integers_eq
-- name    : ModularCurve.FullLevel.exists_regularProlongation_fieldBar_integers_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/081c06f3-0bb5-5a0a-8bd7-a4f3a0003944
-- title:
--   Presented Gauss ring as a regular prolongation at full level
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, and write $\kappa =$ `ResidueField A` for its residue field and $\mathrm{res}_A : A \to \kappa$ for the residue map. Let $F =$ `fieldBar q M'` be the base change to $\overline{\mathbb{Q}}$ of the level-$\Gamma_H$ function field for $H =$ `levelH q M'`, the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, regarded as an intermediate field of $\overline{\mathbb{Q}}((q))$ over $\overline{\mathbb{Q}}$. Let $O$ be a valuation subring of $F$ satisfying the presentation hypothesis: $f \in O$ if and only if there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ to $\kappa$ is nonzero and $f \cdot y = x$ in $\overline{\mathbb{Q}}((q))$ (images under the coefficientwise inclusion $A \hookrightarrow \overline{\mathbb{Q}}$). The conclusion asserts the existence of a regular prolongation $R$ of $A$ to $F$ with residue field $\kappa$-side target `qExpFunctionFieldC` $\kappa$ $\Gamma_H(q^2M')$ — that is, a valuation subring `R.integers` of $F$ together with a surjective ring map to that field whose kernel is the maximal ideal, lying over $A$ in the sense that $\mathrm{algebraMap}\,x \in R.\mathrm{integers} \iff x \in A$ and compatibly with $\mathrm{res}_A$, and such that every nonzero $f \in F$ admits $c \in \overline{\mathbb{Q}}$ with $c \cdot f$ integral of nonzero residue — such that `R.integers` $= O$, and such that for every Laurent series $y$ over $A$ whose image lies in $F$, that image lies in `R.integers` and its residue, viewed as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$.
--
--   This identifies the Gauss (i.e. $q$-expansion) valuation ring of the geometric component field at full level $q$ — given in the presentation form "$f = x/y$ with $y$ having nonzero reduction" — as the integer ring of a regular prolongation of $A$ with residue field the $q$-expansion field over the residue field of $A$, the residues being computed coefficientwise. It serves as the existence input for the statements that this ring is stable, up to the relevant Borel condition, under the level automorphisms at the cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_regularProlongation_fieldBar_integers_eq.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.exists_regularProlongation_fieldBar_integers_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ R : RegularProlongation A (fieldBar q M')
        (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))),
      R.integers = O ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y := by sorry
