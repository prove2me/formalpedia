-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_2_3
-- name    : LocalLemmaHierarchy.Completeness.theorem_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:19:11.679612+00:00
-- url     : https://prove2.me/theorems/02994b44-8097-4db3-b581-a60b1ca4bac6
-- title:
--   Theorem 2.3 — finite exact criterion: zero-freeness ⇔ Shearer positivity ⇔ exact-tree supersolutions
-- statement:
--   Let $\mathcal R$ be a positive local deletion representation of $Z$. For a finite region $U$ and nonnegative moduli $p$, the following are equivalent:
--
--   (i) $Z_U(z)\ne0$ whenever $|z_\tau|\le p_\tau$;
--   (ii) $P_W(p)>0$ for every $W\subseteq U$;
--   (iii) the exact trees of $U$ from all roots have supersolutions satisfying (2.7).
--
--   In this case the bottom-up equality evaluation (here: the depth-$|U|$ evaluation of the exact trees from zero, `exactIter R U p |U|`) is a supersolution, lies below every supersolution, satisfies $\Phi^U_{p,h}(X)=X_h$, and at every occurrence $h$ ending at $v$ equals $X_h=X_{U_h,v}(p)=1-P_{U_h}(p)/P_{U_h-v}(p)$ with $0\le X_h<1$ (2.8).
--
--   Differences from the source:
--   - generalization: the sites form a countable set V → V is any type (no countability assumption); reason: no step of the proofs uses countability; the statement for countable V is the special case
--   - encoding: a total order ≺_{v,a} on D_{v,a} \ {v} → a rank R.rank v a : V → ℕ injective on D_{v,a} \ {v}, with w ≺ u ↔ rank w < rank u; reason: every total order on a finite set is induced by such a rank, and only comparisons are used
--   - encoding: a polynomial family Z = (Z_U)_{U ⋐ V} in the variables z_τ → Z : Finset V → MvPolynomial T ℝ, evaluated at complex z by MvPolynomial.aeval; reason: Z_∅ = 1 and the deletion identity with real c_{v,a} > 0 determine every Z_U recursively, so its coefficients are real; the source families are exactly these
--   - encoding: bottom-up equality evaluation of the exact trees of U → exactIter R U p |U|, the depth-|U| evaluation from zero boundary values; reason: each move deletes its endpoint, so every branch has at most |U| − 1 moves and |U| rounds evaluate every finite exact tree bottom-up
--   - encoding: "is the least supersolution" → it is a supersolution and is ≤ every supersolution at every occurrence; reason: the definition of least element
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Theorem 2.3, printed p. 7 (PDF p. 9); proof App. A.1 with Lemma A.1, printed pp. 13–14 (PDF pp. 15–16)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

/-- **Theorem 2.3 (Finite exact criterion)**, printed p. 7 / PDF 9 (proof App. A.1, printed 13–14).
For a finite region `U` and nonnegative moduli `p`: (i) zero-freeness on the closed polydisc
`|z_τ| ≤ p_τ` ⇔ (ii) `P_W(p) > 0` for every `W ⊆ U` ⇔ (iii) the exact trees of `U` have a
supersolution (2.7). In this case the bottom-up equality evaluation `exactIter R U p |U|` is the least
supersolution, and at every occurrence `h` it equals `X_h = X_{U_h, v(h)}(p) ∈ [0, 1)` (2.8). -/
theorem theorem_2_3 {V T : Type} [DecidableEq V] (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (U : Finset V) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ) :
    (ZeroFreeOn Z U p ↔ ∀ W ⊆ U, 0 < negEval Z W p) ∧
    ((∀ W ⊆ U, 0 < negEval Z W p) ↔ ∃ x : Hist R → ℝ, IsExactSupersolution R (↑U) p x) ∧
    ((∀ W ⊆ U, 0 < negEval Z W p) →
      IsExactSupersolution R (↑U) p (exactIter R (↑U) p U.card) ∧
      (∀ x : Hist R → ℝ, IsExactSupersolution R (↑U) p x →
        ∀ h : Hist R, IsExact R (↑U) h → exactIter R (↑U) p U.card h ≤ x h) ∧
      (∀ h : Hist R, IsExact R (↑U) h →
        exactUpdate R (↑U) p (exactIter R (↑U) p U.card) h = exactIter R (↑U) p U.card h ∧
        exactIter R (↑U) p U.card h = exactRatio R Z U p h ∧
        0 ≤ exactRatio R Z U p h ∧ exactRatio R Z U p h < 1)) := by sorry

end LocalLemmaHierarchy.Completeness
