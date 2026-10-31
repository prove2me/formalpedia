-- Prove2me | Theorems.Thm_LimitedPersuasion_lemma_4
-- name    : LimitedPersuasion.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:45.229429+00:00
-- url     : https://prove2.me/theorems/b9b550f6-1221-4cd2-b860-7a935e9c80ee
-- title:
--   Lemma 4 — every $s$-Pareto collection is realized by a symmetric, direct and persuasive scheme
-- statement:
--   Let $2\le k\le n$, let the instance be symmetric with distinct types, let $s\in\mathbb R$ and let $\mathcal P$ be an $s$-Pareto point collection. Then there is a symmetric, direct and persuasive scheme $\varphi^*$, in which signal $j$ recommends action $j\in[k]$, with
--   $$u_S(\varphi^*)=u_S(\mathcal P),$$
--   where $u_S(\varphi^*)$ is the sender's utility when the receiver follows the recommendation. Moreover the recommendation points of $\varphi^*$ are the points of $\mathcal P$: $p_{\varphi^*}(C)=p(C)$ for every $C$ with $q_C>0$.
--
--   Lemma 4 is the lower-bound half of Theorem 1: every $s$-Pareto collection is achieved by a persuasive scheme.
--
--   Differences from the source:
--   - generalization: conclusion $u_S(\varphi^*)=u_S(\mathcal P)$ → additionally the recommendation points of $\varphi^*$ equal those of $\mathcal P$ (where $q_C\ne0$); reason: a stronger conclusion, which the paper's construction provides ("the point $p(C)$ corresponds to the (conditioned on the given set $C$) expected utilities of $\varphi^*$", p.7), and which implies the printed one
--   - reading: $u_S(\varphi^*)$ → the utility when the receiver follows the recommendation; reason: §3's utility of a direct scheme
--   - reading: symmetric scheme → the conditional-distribution equalities cross-multiplied by the signal probabilities; reason: conditional distributions given a null signal are undefined
--   - reading: Definition 1's conditions for every $C$, frontier and slope defined graphically → for every $C$ with $q_C\ne0$; frontier: no hull point strictly larger in both coordinates (keeps the horizontal and vertical end segments of p.6); slope: real $s\le0$ with the supporting-line inequality on the hull; reason: only those $C$ occur, which makes the hypothesis weaker, so the lemma covers more collections; slope $-\infty$ is not in Definition 1 ("For $s\le0$"; §3.2 uses $[0,-\infty)$)
-- source:
--   Gradwohl–Hahn–Hoefer–Smorodinsky, Algorithms for Persuasion with Limited Communication, arXiv:2007.12489v2, Lemma 4, §3.1, p.8 (construction of φ* pp.7–8)

import Mathlib
import Definitions.Def_LimitedPersuasion_PointCollection

namespace LimitedPersuasion

/-- **Lemma 4**, Gradwohl–Hahn–Hoefer–Smorodinsky, arXiv:2007.12489v2, §3.1, p.8: in a symmetric
instance (with distinct types), for every `s`-Pareto point collection `P` there is a symmetric,
direct, and persuasive signaling scheme `φ*` with `u_S(φ*) = u_S(P)`. Moreover the recommendation
points of `φ*` are the points of `P` (the scheme constructed in the proof, pp.7–8).

**Formalization Note.** `φ*` recommends action `j ∈ [k]` with signal `j`; `u_S(φ*)` is the
sender's utility when the receiver follows the recommendation (`Instance.followS`). The equality
of recommendation points is required for every `C` with `q_C ≠ 0`. -/
theorem lemma_4 {T : Type*} [Fintype T] [DecidableEq T] {n k : ℕ} [NeZero n]
    (I : Instance T n) (hk : 2 ≤ k) (hkn : k ≤ n) (hsym : I.IsSymmetric)
    (hdist : I.DistinctTypes) (s : ℝ) (P : Finset T → ℝ × ℝ) (hP : I.IsSPareto hkn s P) :
    ∃ φ : (Fin n → T) → Fin k → ℝ,
      I.IsSymmetricScheme hkn φ ∧ I.Persuasive φ (Fin.castLE hkn) ∧
        I.followS φ (Fin.castLE hkn) = I.uSP hkn P ∧
        ∀ C : Finset T, I.qC hkn C ≠ 0 → I.recPt hkn φ C = P C := by sorry

end LimitedPersuasion
