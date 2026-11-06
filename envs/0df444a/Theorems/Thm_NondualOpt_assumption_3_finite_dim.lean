-- Prove2me | Theorems.Thm_NondualOpt_assumption_3_finite_dim
-- name    : NondualOpt.assumption_3_finite_dim
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:03:54.130646+00:00
-- url     : https://prove2.me/theorems/9e23cdbd-9ad1-4521-b17c-72d5aa64d202
-- title:
--   Assumption 3 holds for finite-dimensional compact convex $X,H$ with $H=-H$
-- statement:
--   Let $X,H\subseteq\mathbb R^d$ be nonempty, compact and convex, with $H=-H$, and pair them by the dot product. Then for every horizon $T$, Assumption 3 holds: $\Lambda_{X,H}<\infty$ and the minimax interchange ① is valid,
--   $$
--   V^{\max}_{X,H,T}=\Big\langle\!\Big\langle\sup_{r_t}\inf_{s_t}\mathbb E_{x_t\sim s_t,\ \ell_t\sim r_t}\Big\rangle\!\Big\rangle_{t=1}^T\Big\{\sum_{t=1}^T\ell_t(x_t)-\inf_{u\in X}T\max_{t\in[T]}\ell_t(u)\Big\}.
--   $$
--   This is the hypothesis under which Proposition 4 and Theorem 6 apply in the $(p,q)$ setting of Corollary 7, where $X=B_p^d$ and $H=B_{q^*}^d$ are compact convex balls.
--
--   Differences from the source:
--   - encoding: a finite-dimensional real space E with its dual E∗ → ℝ^d with the dot product; reason: every finite-dimensional real space with its dual is linearly isomorphic to this
--   - reading: the distributions r_t, s_t of ① in Assumption 3, with the measurable η-minimizer clause → finitely supported laws; the selection clause is not stated; reason: footnote 6, p.9: finitely supported adversarial laws suffice for the minimax interchanges; for such laws expectations are finite sums and the selection clause is automatic
--   - encoding: H = −H → g ∈ H ⇒ −g ∈ H; reason: equivalent
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, p.9 (paragraph after Assumption 3); proof of Corollary 7, p.30

import Mathlib
import Definitions.Def_NondualOpt_dotPair
import Definitions.Def_NondualOpt_Assumption3

namespace NondualOpt

/-- **Assumption 3 holds for finite-dimensional compact convex sets.** For nonempty compact convex
`X, H ⊆ ℝ^d` with `H = −H`, and every horizon `T`, Assumption 3 holds for the dot-product pairing.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, p.9 ("in particular it holds for
finite-dimensional compact convex sets `X, H`, with `H = −H`"), and proof of Corollary 7, p.30
("Finite-dimensional compact balls satisfy Assumption 3").

**Formalization Note.** A finite-dimensional real space with its dual is `ℝ^d` with the dot product
up to a linear isomorphism. The laws of ① are finitely supported (footnote 6, p.9). -/
theorem assumption_3_finite_dim (d : ℕ) (X H : Set (Fin d → ℝ)) (hXne : X.Nonempty)
    (hXc : IsCompact X) (hXcv : Convex ℝ X) (hHne : H.Nonempty) (hHc : IsCompact H)
    (hHcv : Convex ℝ H) (hHsymm : ∀ g ∈ H, -g ∈ H) (T : ℕ) :
    Assumption3 (dotPair d) X H T := by sorry

end NondualOpt
