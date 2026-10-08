-- Prove2me | Theorems.Thm_MonoSkew_Main_proposition_2_8_i
-- name    : MonoSkew.Main.proposition_2_8_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:06.260458+00:00
-- url     : https://prove2.me/theorems/660059db-1989-4a9b-bb9a-7052de75f9b1
-- title:
--   Proposition 2.8(i) — $\operatorname{zer}(M+S)$ is a closed convex subset of $\mathcal P\times\mathcal D$
-- statement:
--   In the setting of Problems 1.1 and 1.2 ($A$, $B$ maximally monotone, $L$ bounded linear, $z\in\mathcal H$, $r\in\mathcal G$, $M$ and $S$ as in (1.8) on $\mathcal K=\mathcal H\oplus\mathcal G$), the set
--   $$\operatorname{zer}(M+S)=\{(x,v)\in\mathcal K\mid 0\in M(x,v)+S(x,v)\}$$
--   is a closed convex subset of $\mathcal P\times\mathcal D$, where $\mathcal P$ and $\mathcal D$ are the solution sets of the primal inclusion (1.2) and the dual inclusion (1.3).
--
--   Thus every zero of the monotone+skew operator yields a primal solution and a dual solution at once.
--
--   **Formalization Note** "Closed" is in the norm topology of $\mathcal K$ = `WithLp 2 (H × G)`; "subset of $\mathcal P\times\mathcal D$" is stated componentwise: every $(x,v)\in\operatorname{zer}(M+S)$ has $x\in\mathcal P$ and $v\in\mathcal D$.
-- source:
--   Briceño-Arias and Combettes, A Monotone+Skew Splitting Model for Composite Monotone Inclusions in Duality, arXiv:1011.5517v1, p. 8, Proposition 2.8(i)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_MonoSkew_Main_Basic

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace MonoSkew.Main

/-- Proposition 2.8(i) (p. 8): in the setting of Problems 1.1 and 1.2, `zer(M + S)` is a closed
convex subset of `𝒫 × 𝒟`. -/
theorem proposition_2_8_i {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H → Set H) (B : G → Set G) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (L : H →L[ℝ] G) (z : H) (r : G) :
    IsClosed (zer (addSingle (opM A B z r) (opS L))) ∧
    Convex ℝ (zer (addSingle (opM A B z r) (opS L))) ∧
    ∀ p ∈ zer (addSingle (opM A B z r) (opS L)),
      p.fst ∈ primalSet A B L z r ∧ p.snd ∈ dualSet A B L z r := by sorry

end MonoSkew.Main
