-- Prove2me | Theorems.Thm_LimitedPersuasion_lemma_2
-- name    : LimitedPersuasion.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:43.295998+00:00
-- url     : https://prove2.me/theorems/43f7a856-cf33-411c-94d0-434c95a0e741
-- title:
--   Lemma 2 — every direct persuasive scheme is weakly improved by an $s$-Pareto point collection
-- statement:
--   Let $2\le k\le n$ and let $\varphi$ be a direct and persuasive $k$-signal scheme in which signal $j$ recommends action $j\in[k]$. Then there are a slope $s\le 0$ and an $s$-Pareto point collection $\mathcal P$ such that
--   $$u_S(\mathcal P)\ \ge\ u_S(\varphi),$$
--   where $u_S(\varphi)=\sum_\sigma v_\sigma(\sigma)$ is the sender's utility when the receiver follows the recommendation. That is, for every set $C$ of types of the first $k$ actions with $q_C>0$, the point $p(C)$ lies on the Pareto frontier of $C$ and corresponds to the common slope $s$, and $u_R(\mathcal P)\ge\varrho_E$.
--
--   Lemma 2 is the upper-bound half of Theorem 1: no direct persuasive scheme beats the best $s$-Pareto collection.
--
--   Differences from the source:
--   - generalization: §3.1 works in symmetric instances with distinct types → any instance; reason: the statement does not use symmetry or distinctness (it is an optimization over the hulls under one linear constraint), so it specializes to the paper's
--   - reading: "every direct and persuasive scheme" → one recommending action $j$ with signal $j$; reason: §3.1's standing convention, "Due to Lemma 1 we consider a direct and persuasive scheme that recommends actions from the set $[k]$" (p.5), and the proof's "uses signals corresponding to the first $k$ actions"
--   - reading: $u_S(\varphi)$ → the utility when the receiver follows the recommendation; reason: §3's utilities of a direct scheme
--   - reading: conditions of Definition 1 "for every subset $C$", frontier and slope defined graphically → for every $C$ with $q_C\ne0$; frontier: no hull point strictly larger in both coordinates (keeps the horizontal and vertical end segments of p.6); slope: real $s\le0$ with the supporting-line inequality on the hull; reason: only those $C$ occur; slope $-\infty$ is not in Definition 1 ("For $s\le0$"; §3.2 uses $[0,-\infty)$)
-- source:
--   Gradwohl–Hahn–Hoefer–Smorodinsky, Algorithms for Persuasion with Limited Communication, arXiv:2007.12489v2, Lemma 2, §3.1, p.6 (proof pp.6–7)

import Mathlib
import Definitions.Def_LimitedPersuasion_PointCollection

namespace LimitedPersuasion

/-- **Lemma 2**, Gradwohl–Hahn–Hoefer–Smorodinsky, arXiv:2007.12489v2, §3.1, p.6: for every
direct and persuasive scheme `φ` (recommending action `j ∈ [k]` with signal `j`, the §3.1
convention), there is an `s`-Pareto point collection `P` with `u_S(P) ≥ u_S(φ)`.

**Formalization Note.** `u_S(φ)` is the sender's utility when the receiver follows the
recommendation (`Instance.followS`). Symmetry and distinct types are not assumed. -/
theorem lemma_2 {T : Type*} [Fintype T] [DecidableEq T] {n k : ℕ} [NeZero n]
    (I : Instance T n) (hk : 2 ≤ k) (hkn : k ≤ n) (φ : (Fin n → T) → Fin k → ℝ)
    (hφ : IsScheme φ) (hpers : I.Persuasive φ (Fin.castLE hkn)) :
    ∃ (s : ℝ) (P : Finset T → ℝ × ℝ),
      I.IsSPareto hkn s P ∧ I.followS φ (Fin.castLE hkn) ≤ I.uSP hkn P := by sorry

end LimitedPersuasion
