-- Prove2me | Theorems.Thm_IterRoundDet_lemma_3_2
-- name    : IterRoundDet.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:27.528837+00:00
-- url     : https://prove2.me/theorems/48de3069-4025-43f5-9a7b-2cfeb4c497b0
-- title:
--   Lemma 3.2 — the relaxation: $f(a,\mathbf 1_B)\le\log p(\mathbf 1_B)$, with equality for some $a$; $\mathrm{REL}\ge\log\mathrm{OPT}$
-- statement:
--   For every basis $B$ of $\mathcal M$ and every $a$ with $(a,\mathbf 1_B)\in\mathcal R$,
--
--   $$f(a,\mathbf 1_B)\le\log p(\mathbf 1_B),$$
--
--   with equality for some such $a$ when $p(\mathbf 1_B)>0$. In particular $\mathrm{REL}\ge\log\mathrm{OPT}$: every base of positive value is dominated by the value of $f$ at a feasible point. This is the upper-bound half of the approximation guarantee.
--
--   **Formalization Note** The hypothesis $(a,\mathbf 1_B)\in\mathcal R$ forces $p(\mathbf 1_B)>0$, so the logarithm in the inequality is genuine.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
--   - encoding: REL ≥ log OPT, with the maximum REL → for each base B with p(1_B) > 0, a feasible (a, x) with log p(1_B) ≤ f(a, x); reason: REL is not a defined object here; at OPT = 0 the page's log OPT = −∞ asks nothing
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.2, p.13

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.2 (Relaxation), p.13. For every basis `B` of `M` and every `a` with `(a, 1_B) ∈ R`,
`f(a, 1_B) ≤ log p(1_B)`, with equality for some such `a` when `p(1_B) > 0`. In particular `REL ≥ log OPT`.

**Formalization Note.** `(a, 1_B) ∈ R` forces `p(1_B) > 0`, so the logarithm in the first clause is genuine.
`REL ≥ log OPT` is the last clause: every base with positive value is dominated by a feasible point. When
`OPT = 0` the page's `log OPT = −∞` asks nothing. -/
theorem lemma_3_2 {n d : ℕ} {c : Finset (Fin n) → ℝ} (hc : IsStablePoly d c) {M : Matroid (Fin n)}
    (hM : M.E = Set.univ) {B : Finset (Fin n)} (hB : M.IsBase (B : Set (Fin n))) :
    (∀ a, Feasible c M a (ind B) → relaxObj c a (ind B) ≤ Real.log (pEval c (ind B))) ∧
    (0 < pEval c (ind B) → ∃ a, Feasible c M a (ind B) ∧
      relaxObj c a (ind B) = Real.log (pEval c (ind B))) ∧
    (0 < pEval c (ind B) → ∃ a x, Feasible c M a x ∧
      Real.log (pEval c (ind B)) ≤ relaxObj c a x) := by sorry

end IterRoundDet
