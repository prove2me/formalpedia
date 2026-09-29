-- Prove2me | Theorems.Thm_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar
-- name    : ModularCurve.smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/a7ee9c40-5940-53b4-9789-3a398ea2f377
-- title:
--   Reduction of a regular differential x dj on X₀(N) modulo p∤ N
-- statement:
--   Let $p$ be a prime, let $N\ge 1$ be an integer with $p\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbf Q}$ lying over $p$ in the sense that the image of $p$ lies in the non-units of $A$; write $\kappa=\mathrm{ResidueField}\,A$. Let $y$ be a Laurent series with coefficients in $A$. Assume that its coefficientwise image $x$ under the inclusion $A\hookrightarrow\overline{\mathbf Q}$ lies in `modularFunctionFieldBar N`, the subfield of $\overline{\mathbf Q}((q))$ generated over $\overline{\mathbf Q}$ by the coefficientwise image of `modularFunctionFieldFull N`, and that the coefficientwise reduction $\bar x$ of $y$ under $A\to\kappa$ lies in `modularFunctionFieldC κ N`, the subfield of $\kappa((q))$ generated over $\kappa$ by $j_q=q^{-1}\cdot(E_4^3\eta^{-24})$ and its $N$-th $q$-expansion rescaling. Assume further that $x\cdot d j_q$ is a regular differential of `modularFunctionFieldBar N` over $\overline{\mathbf Q}$, i.e. for every place $v$ of this field over $\overline{\mathbf Q}$ it equals $f\cdot d\pi_v$ for some $f$ in the valuation ring of $v$ and $\pi_v$ the chosen uniformiser at $v$, where $j_q$ here denotes the coefficientwise image of the rational $q$-expansion of $j$. Then $\bar x\cdot d j_q$, formed in `modularFunctionFieldC κ N` over $\kappa$ with $j_q$ the $\kappa$-Laurent series $j_q$, is likewise regular at every place of `modularFunctionFieldC κ N` over $\kappa$.
--
--   This is the statement that a regular differential on $X_0(N)$ over $\overline{\mathbf Q}$ whose $q$-expansion coefficient function has $A$-integral coefficients reduces, at a place of $\overline{\mathbf Q}$ above a prime $p\nmid N$, to a regular differential on the reduction of $X_0(N)$ over the residue field; classically it expresses the good reduction of $X_0(N)$ at $p\nmid N$ together with the $q$-expansion principle, in the function-field formulation going back to Deuring's theory of reduction of function fields. It is used in the construction of reductions of weight-two forms, via [`ModularCurve.exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast`](thm.html#ModularCurve.exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open ModularCurve AlgebraicCurve IsLocalRing

theorem ModularCurve.smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hreg : ((⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) •
        KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
              modularFunctionFieldBar N)) ∈ regularDifferentialsBar N)
    (hmem : coeffMap (residue A) y ∈ modularFunctionFieldC (ResidueField A) N) :
    ((⟨coeffMap (residue A) y, hmem⟩ : modularFunctionFieldC (ResidueField A) N) •
        KaehlerDifferential.D (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
            modularFunctionFieldC (ResidueField A) N)) ∈
      regularDifferentials (ResidueField A) (modularFunctionFieldC (ResidueField A) N) := by sorry
