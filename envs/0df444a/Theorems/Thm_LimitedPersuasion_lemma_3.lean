-- Prove2me | Theorems.Thm_LimitedPersuasion_lemma_3
-- name    : LimitedPersuasion.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:46.475343+00:00
-- url     : https://prove2.me/theorems/f6560280-12c7-4716-ab88-286eb31007e9
-- title:
--   Lemma 3 — in symmetric instances a symmetric scheme is persuasive iff $u_R(\varphi)\ge\varrho_E$
-- statement:
--   Let $2\le k\le n$, let the instance be symmetric, and let $\varphi$ be a symmetric scheme (signal $j$ recommends action $j\in[k]$, and the conditional type distributions of recommended actions, of non-recommended actions in $[k]$, and of actions in $[n]\setminus[k]$ do not depend on which actions are involved). Then
--   $$\varphi\ \text{is persuasive}\quad\Longleftrightarrow\quad u_R(\varphi)\ \ge\ \varrho_E,$$
--   where $u_R(\varphi)=\sum_\sigma w_\sigma(\sigma)$ is the receiver's expected utility when following the recommendation.
--
--   For symmetric schemes this reduces the $k\cdot n$ obedience constraints to a single inequality, which is how Lemma 4 obtains persuasiveness.
--
--   Differences from the source:
--   - reading: $u_R(\varphi)$ → the receiver's utility when following the recommendation; reason: §3's utility of a direct scheme; with best-response utility the "only if" direction would be trivial and the "if" direction false
--   - reading: symmetric scheme (equal conditional type distributions) → the equalities cross-multiplied by the signal probabilities; reason: conditional distributions given a null signal are undefined
--   - generalization: the standing assumption that all types are distinct → not assumed; reason: not used, so the statement specializes to the paper's
--   - encoding: each signal recommends a distinct action in $[k]$ → signal $j$ recommends action $j$; reason: relabelling the signals changes no instance
-- source:
--   Gradwohl–Hahn–Hoefer–Smorodinsky, Algorithms for Persuasion with Limited Communication, arXiv:2007.12489v2, Lemma 3, §3.1, p.7 (definition of symmetric scheme p.7; proof pp.7–8)

import Mathlib
import Definitions.Def_LimitedPersuasion_Model

namespace LimitedPersuasion

/-- **Lemma 3**, Gradwohl–Hahn–Hoefer–Smorodinsky, arXiv:2007.12489v2, §3.1, p.7: in symmetric
instances, a symmetric scheme `φ` is persuasive if and only if `u_R(φ) ≥ ϱ_E`.

**Formalization Note.** A symmetric scheme recommends action `j ∈ [k]` with signal `j`
(`Instance.IsSymmetricScheme`); `u_R(φ)` is the receiver's utility when following the
recommendation (`Instance.followR`). Distinct types are not assumed. -/
theorem lemma_3 {T : Type*} [Fintype T] [DecidableEq T] {n k : ℕ} [NeZero n]
    (I : Instance T n) (hk : 2 ≤ k) (hkn : k ≤ n) (hsym : I.IsSymmetric)
    (φ : (Fin n → T) → Fin k → ℝ) (hφ : I.IsSymmetricScheme hkn φ) :
    I.Persuasive φ (Fin.castLE hkn) ↔ I.rhoE ≤ I.followR φ (Fin.castLE hkn) := by sorry

end LimitedPersuasion
