-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/fba3e12e-f857-52bc-ab6d-c1481aa4b091
-- title:
--   One-point moving on X₀(Nq) into the strict locus
-- statement:
--   Let $N$ be a nonzero natural number, $q$ a prime not dividing $N$, and $A$ a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, so that the residue field $\kappa=\mathrm{ResidueField}\,A$ has characteristic $q$. Fix: a finite set $W$ of places of $\kappa$-function field $\mathrm{modularFunctionFieldC}\,\kappa\,N$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in $\mathrm{ssJSet}\,q$); a datum `data` consisting of a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the $q$-expansion pair, together with the Kronecker congruence $\Phi \bmod q=(C(X)^q-X)(C(X)-X^q)$; integrality $h\alpha,h\beta$ of the two degeneracy maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$; a place specialisation $P$ over $A$ at $q$ with target $\kappa$ and reduction $\mathrm{residue}\,A$; and a prolongation tuple $R$ for $P$ (two regular prolongations $R_1,R_2$ of $A$ to $\overline{\mathbb Q}(X_0(Nq))$ with their residue maps) satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node-value law at $W$, and the order law at affine places fixed by the square of $\mathrm{frobOnPlacesGeomLevel}$. Then for every finite set $T$ of places of $\mathrm{modularFunctionFieldC}\,\kappa\,N$ none of which is supersingular, and every place $V_0$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ with $P.\mathrm{reduceFst}\,V_0\in T$ or $P.\mathrm{reduceSnd}\,V_0\in T$, there are a nonzero $f\in\mathrm{modularFunctionFieldBar}(Nq)$ and a divisor $D$ such that $f$ lies in the valuation rings $R_1.\mathrm{integers}$ and $R_2.\mathrm{integers}$ with both residues $R.\mathrm{residue}_1 f$ and $R.\mathrm{residue}_2 f$ nonzero; $D\,V=\mathrm{ord}_V f$ for every place $V$; $D\,V_0=1$; and every $V$ in the support of $D$ other than $V_0$ satisfies $P.\mathrm{IsStrictFst}\,V$ or $P.\mathrm{IsStrictSnd}\,V$ (Frobenius carries one reduction to the other and does not fix it after two steps) and has both reductions $P.\mathrm{reduceFst}\,V$, $P.\mathrm{reduceSnd}\,V$ outside $T$.
--
--   This is the level-$N$ one-point moving lemma on $X_0(Nq)$: it produces a function that is a unit on both prolongations, has a simple zero at a prescribed place whose reduction meets the forbidden set $T$, and has all its other zeros and poles at strict places reducing away from $T$. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel) to move a divisor class into the good locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem.lean

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : P.ProlongationTuple) (hR : R.IsModel) (hNR : R.RegularityLaw W)
      (hval : R.NodeValueLaw W) (hO : R.OrderLawFixed),
        ∀ (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)))
          (hT : ∀ t ∈ T, t ∉ ssPlaces q N (ResidueField A))
          (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
          (hV₀ : P.reduceFst V₀ ∈ T ∨ P.reduceSnd V₀ ∈ T),
          ∃ (f : ↥(modularFunctionFieldBar (N * q)))
            (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
            f ≠ 0 ∧

            (∃ (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
              R.residue₁ ⟨f, h₁⟩ ≠ 0 ∧ R.residue₂ ⟨f, h₂⟩ ≠ 0) ∧
            (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧

            (∀ V ∈ D.support, V ≠ V₀ → P.IsStrictFst V ∨ P.IsStrictSnd V) ∧

              ∀ V ∈ D.support, V ≠ V₀ → P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by sorry
