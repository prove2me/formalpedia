-- Prove2me | Theorems.Thm_MultiIssueMediation_lemma_2
-- name    : MultiIssueMediation.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:04.771019+00:00
-- url     : https://prove2.me/theorems/99e13d29-f366-48a7-9c31-0cf3fddf4703
-- title:
--   Lemma 2 — the row order of bundles persists along the diagonals
-- statement:
--   Let $f$ be a rule whose main diagonal is $f_{k,k}=b_k$, and suppose that adjacency holds on all diagonals $t=2,\dots,k$, where $k\le m$: for all $t\in\{2,\dots,k\}$ and $m\ge\ell>j$ with $\ell=j+t-1$, $f_{\ell,j}\in\{f_{\ell-1,j},f_{\ell,j+1}\}\subset\mathbf B$.
--
--   Let $a=b_u$ and $b=b_v$ with $u<v$, that is, $a$ lies on a higher row than $b$ on the first diagonal. If $a$ and $b$ both appear on a diagonal $t\in\{2,\dots,k\}$, then on every diagonal $s\le t$ both appear, and every occurrence of $a$ lies on a smaller row index than every occurrence of $b$.
--
--   The lemma is the bookkeeping device of the induction in Lemma 3 and of Lemmas 4–6.
--
--   Differences from the source:
--   - generalization: the ambient rule of the proof is efficient, individually rational and strategy-proof → only f_{k,k} = b_k (Part ii) and the stated adjacency are assumed; reason: the lemma's proof uses nothing else, and Part ii gives that hypothesis for every such rule
--   - reading: "lies on a higher row"; a bundle "on" a diagonal → a smaller row index; both bundles occur on each lower diagonal and every occurrence of a is compared with every occurrence of b; reason: the proof says "lies above" and first shows that both appear on every diagonal; a bundle can occur several times on a diagonal
--   - encoding: indices 1, …, m, outside options o_X, o_Y, cells f_{ℓ−1,j}, f_{ℓ,j+1} → Fin m with value = index − 1, Option (Fin m) with none the outside option, Fin.rev for m+1−k, indices p, q with p + 1 = ℓ, q = j + 1; reason: Lean conventions; the instances are the same
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, Lemma 2, p.32

import Mathlib
import Definitions.Def_MultiIssueMediation_RuleGeometry

namespace MultiIssueMediation

/-- **Lemma 2** (Kesten, Özyurt, *Efficient and Incentive Compatible Mediation: An Ordinal Market
Design Approach*, working paper, 4 October 2018, Lemma 2, p.32). Suppose that the main diagonal is
`B` in order (Part ii, in force on the page) and that adjacency holds on all diagonals
`t = 2, …, k` with `k ≤ m`. If `a = b_u` lies on a higher row than `b = b_v` on the first diagonal
(`u < v`) and both appear on diagonal `t ∈ {2, …, k}`, then on every diagonal `s ≤ t` both appear
and `a` lies on a higher row than `b`.

**Formalization Note.** "Higher row" is a smaller row index here (the proof says "lies above"). A
bundle can occur several times on a diagonal, so the conclusion compares every occurrence of `a`
with every occurrence of `b`. No incentive property is assumed. -/
theorem lemma_2 {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m)
    (hdiag : ∀ k : Fin m, f k k = logrollBundle k) (k : ℕ) (hk : k ≤ m)
    (hadj : ∀ t : ℕ, 2 ≤ t → t ≤ k → ∀ ℓ j p q : Fin m, OnDiagonal t ℓ j →
      p.val + 1 = ℓ.val → q.val = j.val + 1 → AdjacentCell f ℓ j p q)
    (u v : Fin m) (huv : u < v) (t : ℕ) (ht2 : 2 ≤ t) (htk : t ≤ k)
    (hu : ∃ ℓ j : Fin m, OnDiagonal t ℓ j ∧ f ℓ j = logrollBundle u)
    (hv : ∃ ℓ j : Fin m, OnDiagonal t ℓ j ∧ f ℓ j = logrollBundle v) :
    ∀ s : ℕ, 1 ≤ s → s ≤ t →
      (∃ ℓ j : Fin m, OnDiagonal s ℓ j ∧ f ℓ j = logrollBundle u) ∧
        (∃ ℓ j : Fin m, OnDiagonal s ℓ j ∧ f ℓ j = logrollBundle v) ∧
        ∀ ℓ j ℓ' j' : Fin m, OnDiagonal s ℓ j → OnDiagonal s ℓ' j' →
          f ℓ j = logrollBundle u → f ℓ' j' = logrollBundle v → ℓ < ℓ' := by sorry

end MultiIssueMediation
