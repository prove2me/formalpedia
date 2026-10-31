-- Prove2me | Theorems.Thm_LPAllocRM_accepted_lpPolicy
-- name    : LPAllocRM.accepted_lpPolicy
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:07:16.341819+00:00
-- url     : https://prove2.me/theorems/981c1ccf-97b0-48f5-84f8-7a2e2bc4096e
-- title:
--   The booking-limit identity (5): $N^{LP}_j=D_j(\tau)\wedge\lfloor x^*_j\rfloor$
-- statement:
--   Let $d$ be an arrival path on $(0,\tau]$ (finitely many arrivals, at most one at any time), $y\in\mathbb R^n$ an allocation vector and $\pi$ the allocation policy $\pi_j(t)=1(D_j(t)\le y_j)$. Then for every class $j$ the number of accepted class-$j$ customers is
--
--   $$N_j=D_j(\tau)\wedge\lfloor y_j\rfloor,$$
--
--   where $a\wedge b=\min\{a,b\}$ and $\lfloor r\rfloor$ is the largest integer not exceeding $r$ (taken as $0$ when $r<0$).
--
--   With $y=x^*$ this is (5), $N^{LP}_j=D_j(\tau)\wedge\lfloor x^*_j\rfloor$; with $y=kx^*$ it is its form in the $k$th problem, $N^{LP(k)}_j=D^{(k)}_j(\tau)\wedge\lfloor kx^*_j\rfloor$, used in the proof of Proposition 1.
--
--   Differences from the source:
--   - generalization: allocations x* and kx* (optimal LP solutions, hence ⩾ 0) → every real allocation vector y; reason: the identity holds for all y and specializes to y = x* and y = kx*
--   - generalization: horizon (0, τ] with τ > 0 → any real τ; reason: τ > 0 is not used; the statement specializes to the paper's horizon
--   - encoding: ⌊r⌋ ≡ max{i ∈ ℤ : i ⩽ r} → Nat.floor (⌊r⌋₊, which is 0 for r < 0); reason: the two agree for r ⩾ 0, which covers x*_j and kx*_j
--   - encoding: a sample path of the simple point process D(·) → d : ℝ → Fin n → ℕ with IsArrivalPath τ d; reason: the counting path of a simple point process with finitely many points in (0, τ]
--   - encoding: N^π_j ≡ ∫_(0,τ] π_j(s) D_j(ds), (2) → accepted: the number of i ∈ {1, …, D_j(τ)} such that π accepts class j at the i-th class-j arrival time, given the path up to that time; reason: on a simple counting path the Stieltjes integral (2) is exactly this count
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, eq. (5), p.723; applied to problem k in the proof of Proposition 1, p.724

import Mathlib
import Definitions.Def_LPAllocRM_IsArrivalPath
import Definitions.Def_LPAllocRM_accepted
import Definitions.Def_LPAllocRM_lpPolicy

namespace LPAllocRM

/-- The booking-limit identity (5): on every arrival path (finitely many arrivals in `(0, τ]`, at most
one at a time), the allocation policy with allocation `y` accepts exactly
`N_j = D_j(τ) ∧ ⌊y_j⌋` class-`j` customers, for every class `j`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
(5), p.723 (PDF p.4), with `y = x*`; applied to the kth problem with `y = k x*` in the proof of
Proposition 1, p.724 (PDF p.5): "N^LP(k)_j = D^(k)_j(τ) ∧ ⌊kx∗_j⌋".

**Formalization Note** Stated pathwise for every real allocation vector `y`, which covers `x*`
and `k x*`. `⌊·⌋₊` is `Nat.floor`; for `y_j ≥ 0` (as for `x*`, which is LP-feasible) it equals the
paper's integer floor `⌊r⌋ ≡ max{i ∈ ℤ : i ⩽ r}`, and for `y_j < 0` it is `0`, the number of
customers `π` then accepts. -/
theorem accepted_lpPolicy {n : ℕ} (τ : ℝ) (d : ℝ → Fin n → ℕ) (hd : IsArrivalPath τ d)
    (y : Fin n → ℝ) (j : Fin n) :
    accepted τ (lpPolicy y) d j = min (d τ j) ⌊y j⌋₊ := by sorry

end LPAllocRM
