-- Prove2me | Theorems.Thm_OnlineCarpoolingLei_Oblivious_admissible_selections
-- name    : OnlineCarpoolingLei.Oblivious.admissible_selections
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:05.02558+00:00
-- url     : https://prove2.me/theorems/91311172-2501-4c37-bf93-7b1fe086f97d
-- title:
--   Theorem 3.3 — the admissible selections form a nonempty compact convex subset of $B$
-- statement:
--   Let $u\ne v$ be elements of $[n]$, put $e=\mathbf 1_u-\mathbf 1_v$, and let $\mu$ be a finitely supported probability measure on $\mathbb R^n$ with $\mu\preceq_{cx}\gamma$, where $\gamma=N(0,50I_n)$. Then the set of selections $p\in B=\prod_{x\in\operatorname{supp}\mu}B_x$ that are admissible for $(\mu,e)$, that is with
--   $$\mu^{p,e}=\sum_{x\in\operatorname{supp}\mu}\mu(\{x\})\big(p(x)\delta_{x+e}+(1-p(x))\delta_{x-e}\big)\preceq_{cx}\gamma,$$
--   is a nonempty, compact and convex subset of $B$.
--
--   The statement concerns every finitely supported law on $\mathbb R^n$ dominated by $\gamma$, not only the laws reached by the algorithm. It is the selection theorem that makes the algorithm of Section 3.2 well defined: the minimal-norm admissible selection exists and is unique.
--
--   Differences from the source:
--   - encoding: vertex set $[n]$ → `Fin n`; reason: relabelling
--   - encoding: finitely supported probability measure $\mu$ on $\mathbb R^n$ → nonnegative weights `μ : (Fin n → ℝ) →₀ ℝ` summing to one, support = points of positive mass; reason: a finitely supported probability measure is determined by its atoms
--   - encoding: selections, an element of $[0,1]^{\operatorname{supp}\mu}$ → real functions on the support subtype with the product topology; reason: $B\subseteq[0,1]^{\operatorname{supp}\mu}$, so the admissible set is the same subset of the same finite-dimensional space
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Theorem 3.3, p.5 (PDF p.5); proof in Section 6, p.13

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Model
import Definitions.Def_OnlineCarpoolingLei_Oblivious_ConvexOrder

namespace OnlineCarpoolingLei.Oblivious

/-- Theorem 3.3 (p.5). Let `u ≠ v` in `[n]`, `e = 1_u − 1_v`, and let `μ` be a finitely
supported probability measure on `ℝⁿ` with `μ ⪯cx γ`. Then the set of admissible selections
for `(μ, e)` is a nonempty, compact and convex subset of `B`. -/
theorem admissible_selections {n : ℕ} (e : Edge n) (μ : (Fin n → ℝ) →₀ ℝ) (hμ : IsFinProb μ)
    (hdom : CxLeGamma μ) :
    (admissible μ e).Nonempty ∧ IsCompact (admissible μ e) ∧ Convex ℝ (admissible μ e) ∧
      admissible μ e ⊆ selBox μ e := by sorry

end OnlineCarpoolingLei.Oblivious
