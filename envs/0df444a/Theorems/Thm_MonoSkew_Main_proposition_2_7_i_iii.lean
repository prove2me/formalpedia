-- Prove2me | Theorems.Thm_MonoSkew_Main_proposition_2_7_i_iii
-- name    : MonoSkew.Main.proposition_2_7_i_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:10.611345+00:00
-- url     : https://prove2.me/theorems/3e48beb5-059e-4802-96b3-1466dfa91a9c
-- title:
--   Proposition 2.7(i)–(iii) — $M$ and $M+S$ are maximally monotone; $S$ is bounded, skew, with $\|S\|=\|L\|$
-- statement:
--   Let $\mathcal H$, $\mathcal G$ be real Hilbert spaces, let $A:\mathcal H\to2^{\mathcal H}$ and $B:\mathcal G\to2^{\mathcal G}$ be maximally monotone, let $L:\mathcal H\to\mathcal G$ be bounded linear, let $z\in\mathcal H$ and $r\in\mathcal G$, and on $\mathcal K=\mathcal H\oplus\mathcal G$ let
--   $$M:(x,v)\mapsto(-z+Ax)\times(r+B^{-1}v),\qquad S:(x,v)\mapsto(L^*v,-Lx).$$
--   Then:
--   1. $M$ is maximally monotone;
--   2. $S$ is a bounded linear operator on $\mathcal K$, $S^*=-S$, and $\|S\|=\|L\|$;
--   3. $M+S$ is maximally monotone.
--
--   These facts make Problem 1.2, $0\in Mx+Sx$, an instance of the monotone inclusion solved by the forward–backward–forward method, with the Lipschitz constant $\|L\|$ for $S$.
--
--   **Formalization Note** "$S\in\mathcal B(\mathcal K)$" is encoded as the existence of a continuous linear operator $T$ on $\mathcal K$ that agrees with $S$ pointwise; $S^*=-S$ and $\|S\|=\|L\|$ are then statements about the adjoint and the operator norm of $T$. $\mathcal K$ is `WithLp 2 (H × G)`. The hypotheses of Problem 1.1 (both operators maximally monotone) are kept in full.
-- source:
--   Briceño-Arias and Combettes, A Monotone+Skew Splitting Model for Composite Monotone Inclusions in Duality, arXiv:1011.5517v1, p. 8, Proposition 2.7(i)–(iii)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_MonoSkew_Main_Basic

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace MonoSkew.Main

/-- Proposition 2.7(i)–(iii) (p. 8): in the setting of Problems 1.1 and 1.2, `M` is maximally
monotone; `S` is a bounded linear operator on `𝒦` with `S* = −S` and `‖S‖ = ‖L‖`; and
`M + S` is maximally monotone. -/
theorem proposition_2_7_i_iii {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H → Set H) (B : G → Set G) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (L : H →L[ℝ] G) (z : H) (r : G) :
    IsMaximalMonotone (opM A B z r) ∧
    (∃ T : K H G →L[ℝ] K H G, (∀ p, T p = opS L p) ∧
      ContinuousLinearMap.adjoint T = -T ∧ ‖T‖ = ‖L‖) ∧
    IsMaximalMonotone (addSingle (opM A B z r) (opS L)) := by sorry

end MonoSkew.Main
