-- Prove2me | Theorems.Thm_MonotoneCompStatics_QSMChar_Supplement_theorem3
-- name    : MonotoneCompStatics.QSMChar.Supplement.theorem3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T04:09:04.339418+00:00
-- url     : https://prove2.me/theorems/ba52706a-ba45-4dbb-b8e6-b214f2b6a475
-- title:
--   Theorem 3 — Ordinal and differential crossing (corrected: strict converse refuted)
-- statement:
--   Let $U:\mathbb R^3\to\mathbb R$ be completely regular, twice continuously differentiable, with $U_y$ everywhere nonzero. With lexicographic order on $(x,y)$,
--   $$\operatorname{SCP}_{\rm lex}(U)\ \Longleftrightarrow\ \operatorname{SM}(U),\qquad\operatorname{strictSM}(U)\ \Longrightarrow\ \operatorname{strictSCP}_{\rm lex}(U).$$
--   The printed converse of the second implication is false. The same item asserts that $U_0(x,y,t)=tx^3+y$ meets every stated regularity and nonvanishing hypothesis and has strict lexicographic single crossing, but fails strict Spence–Mirrlees. Its ratio is $3tx^2$, constant in $t$ at $x=0$.
--
--   This corrected target retains the valid weak equivalence and strict sufficient condition while making the source error explicit. **Formalization Note** The absolute denominator $|U_y|$, all real arguments and both comparison implications are retained. No condition $U_x\ne0$ is added.
--
--   Differences from the source:
--   - encoding: products and set-valued notation → curried functions, dependent profiles and predicates with actual extrema; reason: the order, quantifiers and all conclusion clauses are preserved
--   - correction: strict single crossing implies strict Spence–Mirrlees → retain the weak iff and strict sufficient implication; assert a smooth counterexample to the strict converse; reason: U=tx³+y satisfies every printed premise but its marginal ratio is constant in t at x=0; see DISPROOF.md
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), DOI 10.2307/2951479, p.161, PDF 6, Theorem 3

import Mathlib
import Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_Utility

namespace MonotoneCompStatics.QSMChar.Supplement

/-- Corrected: weak equivalence, strict sufficient direction, and a counterexample
to the printed strict necessary direction, without adding a nonzero U_x premise. -/
theorem theorem3 (U : ℝ → ℝ → ℝ → ℝ) (hreg : CompletelyRegular U)
    (h2 : ContDiff ℝ 2 (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2))
    (hy : ∀ x y t : ℝ, deriv (fun b => U x b t) y ≠ 0) :
    (LexSingleCrossing U ↔ SpenceMirrlees U) ∧
    (StrictSpenceMirrlees U → LexStrictSingleCrossing U) ∧
    (CompletelyRegular cubicUtility ∧
      ContDiff ℝ 2 (fun p : (ℝ × ℝ) × ℝ => cubicUtility p.1.1 p.1.2 p.2) ∧
      (∀ x y t : ℝ, deriv (fun b => cubicUtility x b t) y ≠ 0) ∧
      LexStrictSingleCrossing cubicUtility ∧ ¬ StrictSpenceMirrlees cubicUtility) := by sorry

end MonotoneCompStatics.QSMChar.Supplement
