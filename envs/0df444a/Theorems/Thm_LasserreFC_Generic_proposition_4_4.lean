-- Prove2me | Theorems.Thm_LasserreFC_Generic_proposition_4_4
-- name    : LasserreFC.Generic.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:21.482772+00:00
-- url     : https://prove2.me/theorems/f336aa49-7646-45f4-ad13-0b311505f606
-- title:
--   Proposition 4.4, p. 14 — what items (a)–(d) of Condition 4.3 give at a critical point: few active constraints, CQC, nonzero multipliers, det H(u) ≠ 0
-- statement:
--   Let $m_1\le n$, let $(f,h,g)$ be admissible for the degrees $d_0$, $d_i$, $d'_j$, let $u\in K$, and let $\lambda\in\mathbb R^{m_1}$, $\mu\in\mathbb R^{m_2}$ satisfy
--   $$\nabla f(u)=\sum_{i=1}^{m_1}\lambda_i\nabla h_i(u)+\sum_{j=1}^{m_2}\mu_j\nabla g_j(u),\qquad \mu_jg_j(u)=0\ (j\in[m_2]),$$
--   without the sign conditions $\mu_j\ge0$. Then:
--   1. item (a) of Condition 4.3 implies that at most $n-m_1$ of the $g_j$ are active at $u$;
--   2. items (a) and (b) imply that the constraint qualification condition holds at $u$;
--   3. items (a) and (c) imply $\lambda_i\neq0$ for all $i\in[m_1]$ and $\mu_j\neq0$ for all $j\in J(u)$;
--   4. items (a) and (d) imply $\det H(u)\neq0$.
--
--   These four implications are the link between the algebraic Condition 4.3 and the optimality conditions; Proposition 4.5 combines them with Lemma 4.6.
--
--   **Formalization Note** The page states ii)–iv) with items (b), (c), (d) alone. Those items only concern active sets of size at most $n-m_1$, and without (a) item ii) fails: for $n=1$, $m_1=0$, $g_1=x+x^2$, $g_2=-x+x^2$, $u=0$, item (b) holds but both constraints are active with gradients $1$ and $-1$. Item (a) is therefore added to ii)–iv); it is part of Condition 4.3, so Proposition 4.5 and Theorem 1.2 are unaffected.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 14, Proposition 4.4

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting
import Definitions.Def_LasserreFC_Generic_Cond43

namespace LasserreFC.Generic

open MvPolynomial

/-- Proposition 4.4, p. 14. Let `m₁ ≤ n`, `(f, h, g)` admissible for `(d₀, d, d')`, `u ∈ K`, and
`λ, μ` satisfy (1.3)–(1.4) without the sign conditions `μⱼ ≥ 0`. Then
i) item (a) of Condition 4.3 implies that at most `n − m₁` of the `gⱼ` are active at `u`;
ii) items (a) and (b) imply the constraint qualification condition at `u`;
iii) items (a) and (c) imply `λᵢ ≠ 0` for all `i ∈ [m₁]` and `μⱼ ≠ 0` for all `j ∈ J(u)`;
iv) items (a) and (d) imply `det H(u) ≠ 0`.
Item (a) is added to ii)–iv) (the page states them with (b), (c), (d) alone). -/
theorem proposition_4_4 {n m1 m2 : ℕ} (hm1 : m1 ≤ n) (P : POP n m1 m2) (d0 : ℕ)
    (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) (hadm : P.Admissible d0 d d')
    (u : Fin n → ℝ) (hu : u ∈ P.K) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ)
    (h13 : grad P.f u = ∑ i, lam i • grad (P.h i) u + ∑ j, mu j • grad (P.g j) u)
    (h14 : ∀ j, mu j * eval u (P.g j) = 0) :
    (Cond43a P d d' →
        (Finset.univ.filter fun j => eval u (P.g j) = 0).card ≤ n - m1) ∧
      (Cond43a P d d' → Cond43b P d d' → CQC P u) ∧
      (Cond43a P d d' → Cond43c P d0 d d' →
        (∀ i, lam i ≠ 0) ∧ ∀ j, eval u (P.g j) = 0 → mu j ≠ 0) ∧
      (Cond43a P d d' → Cond43d P d0 d d' → (Hmat P u lam mu).det ≠ 0) := by sorry

end LasserreFC.Generic
