-- Prove2me | Theorems.Thm_MonoSkew_Main_proposition_2_8_ii_vi
-- name    : MonoSkew.Main.proposition_2_8_ii_vi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:29.468314+00:00
-- url     : https://prove2.me/theorems/ce73e73b-fe85-484d-8465-62639e7ee9b1
-- title:
--   Proposition 2.8(ii)–(vi) — solvability of the primal, the dual and the monotone+skew problems are equivalent
-- statement:
--   In the setting of Problems 1.1 and 1.2 ($A$, $B$ maximally monotone, $L$ bounded linear, $z\in\mathcal H$, $r\in\mathcal G$, $M$ and $S$ as in (1.8)), the following are equivalent:
--   1. (ii) $z\in\operatorname{ran}\big(A+L^*\circ B\circ(L\cdot-r)\big)$;
--   2. (iii) $\mathcal P\neq\varnothing$;
--   3. (iv) $\operatorname{zer}(M+S)\neq\varnothing$;
--   4. (v) $\mathcal D\neq\varnothing$;
--   5. (vi) $-r\in\operatorname{ran}\big(-L\circ A^{-1}\circ(z-L^*\cdot)+B^{-1}\big)$.
--
--   In particular the primal problem (1.2) has a solution exactly when the dual problem (1.3) has one, and both are then obtained from the zeros of $M+S$.
--
--   **Formalization Note** The five conditions form a `List.TFAE`. With the definitions of the mission, (ii)⇔(iii) and (v)⇔(vi) hold by unfolding (the paper calls them "clear"); the content is (iii)⇔(iv)⇔(v). The ranges are written as "there is a point whose image contains the value".
-- source:
--   Briceño-Arias and Combettes, A Monotone+Skew Splitting Model for Composite Monotone Inclusions in Duality, arXiv:1011.5517v1, pp. 8–9, Proposition 2.8(ii)–(vi)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_MonoSkew_Main_Basic

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace MonoSkew.Main

/-- Proposition 2.8(ii)–(vi) (pp. 8–9): in the setting of Problems 1.1 and 1.2, the following are
equivalent: (ii) `z ∈ ran(A + L* ∘ B ∘ (L · − r))`; (iii) `𝒫 ≠ ∅`; (iv) `zer(M + S) ≠ ∅`;
(v) `𝒟 ≠ ∅`; (vi) `−r ∈ ran(−L ∘ A⁻¹ ∘ (z − L*·) + B⁻¹)`. -/
theorem proposition_2_8_ii_vi {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H → Set H) (B : G → Set G) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (L : H →L[ℝ] G) (z : H) (r : G) :
    List.TFAE
      [∃ x, z ∈ primalOp A B L r x,
       (primalSet A B L z r).Nonempty,
       (zer (addSingle (opM A B z r) (opS L))).Nonempty,
       (dualSet A B L z r).Nonempty,
       ∃ v, -r ∈ dualOp A B L z v] := by sorry

end MonoSkew.Main
