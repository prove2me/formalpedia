-- Prove2me | Theorems.Thm_ModularCurve_IsPlaceReductionModL_coordinate_clauses
-- name    : ModularCurve.IsPlaceReductionModL.coordinate_clauses
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/24613cdb-66a8-5ff0-bd7a-acfe21617afe
-- title:
--   Reduction mod ℓ acts coordinatewise on j and j_N
-- statement:
--   Fix a nonzero natural number $N$ and a prime $\ell$ with $\ell \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ lying over $\ell$ in the sense that $\ell$ belongs to the nonunits of $A$, with residue field $k =$ `ResidueField A` assumed algebraically closed of characteristic $\ell$. Let $F =$ `modularFunctionFieldBar N`, the subfield of $\overline{\mathbf{Q}}((q))$ generated over $\overline{\mathbf{Q}}$ by the coefficientwise images of `modularFunctionFieldFull N`, and let $\bar F =$ `modularFunctionFieldFullC k N` be the corresponding field over $k$ inside $k((q))$. Let $r$ send places of $F/\overline{\mathbf{Q}}$ to places of $\bar F/k$ and satisfy `IsPlaceReductionModL A N r`: $r$ preserves the residue degree of every place, and for every Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbf{Q}}((q))$ lies in $F$ and whose coefficientwise reduction lies in $\bar F$ and is nonzero, the pushforward along $r$ of the divisor of $y$ is the divisor of that reduction. Write $j =$ `coeffEmb _ jq` $\in F$ and $j_N =$ `coeffEmb _ (qExpand ℚ N jq)` $\in F$, and $\bar\jmath =$ `jqModC k`, $\bar\jmath_N =$ `jqNModC k N` $\in \bar F$. Then four clauses hold: for every place $w$ of $F/\overline{\mathbf{Q}}$ and every $a \in A$, if $\operatorname{ord}_w(j - a) > 0$ then $\operatorname{ord}_{r(w)}(\bar\jmath - \bar a) > 0$, where $\bar a$ is the residue of $a$; if instead $\operatorname{ord}_w(j - a) \le 0$ for all $a \in A$, then $\operatorname{ord}_{r(w)}(\bar\jmath) < 0$; and the same two implications with $j$, $\bar\jmath$ replaced by $j_N$, $\bar\jmath_N$.
--
--   This is Deuring's description of reduction of places of the function field of $X_0(N)$ at a prime $\ell \nmid N$ as reduction of the coordinates of the centre: a place centred at an $A$-integral point $(j, j_N) = (a, b)$ of the plane model goes to the place centred at $(\bar a, \bar b)$, while a place with a non-integral coordinate goes to a pole of that coordinate. It is used to identify the image under $r$ of the cusp at infinity and to compare place specialisation with the induced map on degree-zero Picard groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsPlaceReductionModL_coordinate_clauses.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve AlgebraicCurve IsLocalRing
set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.IsPlaceReductionModL.coordinate_clauses
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hr : IsPlaceReductionModL A N r) :
    (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
      0 < w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
      0 < (r w).ord
          (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
                (IsLocalRing.residue ↥A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A,
        w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r w).ord (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩
        : modularFunctionFieldFullC (ResidueField ↥A) N) < 0) ∧
    (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
      0 < w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
      0 < (r w).ord
          (⟨jqNModC (ResidueField ↥A) N,
              modularFunctionFieldC_le_full (ResidueField ↥A) N (jqNModC_mem (ResidueField ↥A) N)⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
                (IsLocalRing.residue ↥A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A,
        w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r w).ord (⟨jqNModC (ResidueField ↥A) N,
          modularFunctionFieldC_le_full (ResidueField ↥A) N (jqNModC_mem (ResidueField ↥A) N)⟩
        : modularFunctionFieldFullC (ResidueField ↥A) N) < 0) := by sorry
