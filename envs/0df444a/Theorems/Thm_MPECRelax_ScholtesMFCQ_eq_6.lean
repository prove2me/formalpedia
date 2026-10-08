-- Prove2me | Theorems.Thm_MPECRelax_ScholtesMFCQ_eq_6
-- name    : MPECRelax.ScholtesMFCQ.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:11.189988+00:00
-- url     : https://prove2.me/theorems/07d5f577-5ca2-4778-a378-b60eb72a6e4c
-- title:
--   (6) — index sets of R^S(t) near x*
-- statement:
--   Let the data of the MPEC (1) be continuously differentiable and let $x^*$ be feasible for (1). Then there is a neighbourhood $N$ of $x^*$, independent of $t$, such that for every $t>0$ and every $x\in N\cap X^S(t)$:
--   $$I_g(x)\subseteq I_g,\qquad I_G(x)\subseteq I_{00}\cup I_{0+},\qquad I_H(x)\subseteq I_{00}\cup I_{+0},\qquad I_{GH}(x;t)\cap I_G(x)=\emptyset,\qquad I_{GH}(x;t)\cap I_H(x)=\emptyset .$$
--   Here $I_g, I_{00}, I_{0+}, I_{+0}$ are the index sets at $x^*$ and $I_g(x), I_G(x), I_H(x), I_{GH}(x;t)$ the active sets at $x$ (p. 9).
--
--   These inclusions say that near $x^*$ the relaxed program $R^S(t)$ has no active constraints beyond those that the tightened program at $x^*$ controls.
--
--   **Formalization Note.** The paper says "for all $x\in X^S(t)$ sufficiently close to $x^*$" with $t$ fixed by Theorem 3.2's context; we state one neighbourhood for all $t>0$ (the inclusions use only continuity, the disjointness only $t>0$). $I_{GH}(x)$ in (6) is $I_{GH}(x;t)$.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 11, proof of Theorem 3.2, (6)

import Mathlib
import Definitions.Def_MPECRelax_ScholtesMFCQ_Basic

open Filter Topology
open scoped RealInnerProductSpace

namespace MPECRelax.ScholtesMFCQ

/-- (6), proof of Theorem 3.2 (p. 11): there is a neighbourhood `N` of the MPEC-feasible
point `xs`, the same for every `t > 0`, such that every `x ∈ N ∩ X^S(t)` satisfies
`I_g(x) ⊆ I_g`, `I_G(x) ⊆ I_00 ∪ I_0+`, `I_H(x) ⊆ I_00 ∪ I_+0`,
`I_GH(x; t) ∩ I_G(x) = ∅` and `I_GH(x; t) ∩ I_H(x) = ∅`. -/
theorem eq_6 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1) (xs : MPECRelax.ScholtesConv.E n)
    (hfeas : P.Feasible xs) :
    ∃ N ∈ 𝓝 xs, ∀ t : ℝ, 0 < t → ∀ x ∈ N, (P.RS t).Feasible x →
      P.Ig x ⊆ P.Ig xs ∧ P.IG x ⊆ P.I00 xs ∪ P.I0p xs ∧ P.IH x ⊆ P.I00 xs ∪ P.Ip0 xs ∧
        P.IGH x t ∩ P.IG x = ∅ ∧ P.IGH x t ∩ P.IH x = ∅ := by sorry

end MPECRelax.ScholtesMFCQ
