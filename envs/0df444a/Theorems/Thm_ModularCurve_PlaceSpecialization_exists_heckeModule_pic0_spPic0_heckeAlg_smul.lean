-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_heckeModule_pic0_spPic0_heckeAlg_smul
-- name    : ModularCurve.PlaceSpecialization.exists_heckeModule_pic0_spPic0_heckeAlg_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/671c866d-34ed-59af-9d68-ff1a1f5c2b4a
-- title:
--   Hecke-equivariance of the Pic⁰ specialisation map
-- statement:
--   Fix natural numbers $N$ (nonzero) and $q$, with $q$ prime and $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, i.e. the image of $q$ in the ambient field lies in the non-units of $A$. The statement then installs the consequent instances: $q \neq 0$, $q$ prime as a `Fact`, the residue field $k =$ `ResidueField A` has characteristic $q$ (by [`ValuationSubring.charP_residueField_of_liesOverPrime_def`](def/WeierstrassCurve_ReductionMap.html#L57)), the `heckeModuleBar` module structures of the Hecke algebra `HeckeAlg` $= \mathbb{Z}[X_p : p \text{ prime}]$ on `JZero (N * q)` and on `JZero N` (given by evaluating at the commuting Hecke operators when these commute, and by the zero evaluation otherwise), together with decidable equality on $k$ and the $k$-algebra structure on the level-$N$ modular function field used in the semistable setting. For every `data : ModularPolynomialData q`, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions, every proof `hKr` of the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$ for `data`, every pair of proofs that the maps `heckeAlphaBar` and `heckeBetaBar` over $\overline{\mathbb{Q}}$ at level $N$ and prime $q$ are integral, and every place specialisation $P$ of type `PlaceSpecialization A q N data hKr k (IsLocalRing.residue A) hα hβ`, there exists a `HeckeAlg`-module structure on $\mathrm{Pic}^0$ of `modularFunctionFieldC k N` over $k$ — the group of degree-zero divisors on places modulo principal divisors — for which the additive map `P.spPic0 : JZero N →+ Pic0 k (modularFunctionFieldC k N)` is `HeckeAlg`-linear: $P.\mathrm{spPic0}(T \cdot y) = T \cdot P.\mathrm{spPic0}(y)$ for all $T \in$ `HeckeAlg` and all $y \in$ `JZero N` $= \mathrm{Pic}^0$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$.
--
--   This is the Hecke-equivariance of reduction of the Jacobian of $X_0(N)$ at a place of residue characteristic $q \nmid N$: the Hecke action on the characteristic-zero degree-zero divisor class group descends through the specialisation map to an action in characteristic $q$, the operator $T_q$ descending to the geometric Frobenius-type operator supplied by the Kronecker congruence. It feeds the construction of models and widths for place specialisations, being cited by [`ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeGen_smul_eq_heckePic0Fibre_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeGen_smul_eq_heckePic0Fibre_of_isModel) and [`ModularCurve.exists_width_comp_sp`](thm.html#ModularCurve.exists_width_comp_sp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_heckeModule_pic0_spPic0_heckeAlg_smul.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_heckeModule_pic0_spPic0_heckeAlg_smul (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
      ∃ (_ : Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
                (∀ (T : HeckeAlg) (y : JZero N), P.spPic0 (T • y) = T • P.spPic0 y) := by sorry
