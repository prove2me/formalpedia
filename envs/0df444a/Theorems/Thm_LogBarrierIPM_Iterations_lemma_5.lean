-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_lemma_5
-- name    : LogBarrierIPM.Iterations.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:06:39.002401+00:00
-- url     : https://prove2.me/theorems/79b98a05-49e1-4351-be04-8c394c34db56
-- title:
--   Lemma 5 — a tropical segment tsegm(u,v) with u ≤ v is a polygonal curve with directions $e^{K_1},\dots,e^{K_\ell}$, $K_1\subsetneq\dots\subsetneq K_\ell$, $\ell\le d$
-- statement:
--   Let $u,v\in\mathbb T^d$ with $u\le v$ coordinatewise. Then
--   $$\mathsf{tsegm}(u,v)=\{u\}\cup\{u\oplus(\mu\odot v):\ \mu\in\mathbb R,\ \mu\le0\},$$
--   and the curve $\mu\mapsto u\oplus(\mu\odot v)$, which ends at $v$ for $\mu=0$, is polygonal with nested directions: there exist $\ell\le d$, non-empty sets $K_1\subsetneq K_2\subsetneq\dots\subsetneq K_\ell\subseteq[d]$, and breakpoints $c_0<c_1<\dots<c_\ell=0$ in $\mathbb R\cup\{-\infty\}$ such that
--
--   1. $u\oplus(\mu\odot v)=u$ for every real $\mu\le c_0$;
--   2. for every $k\in\{1,\dots,\ell\}$ and all reals $c_{k-1}\le\mu\le\mu'\le c_k$,
--   $$u\oplus(\mu'\odot v)=u\oplus(\mu\odot v)+(\mu'-\mu)\,e^{K_k},$$
--   where $e^K$ is the vector with entry $1$ at the coordinates in $K$ and $0$ elsewhere.
--
--   In words: oriented from $u$ to $v$, the tropical segment consists of ordinary segments supported by direction vectors $e^{K_1},\dots,e^{K_\ell}$ with $K_1\subsetneq\dots\subsetneq K_\ell$ and $\ell\le d$. This is the shape the paper uses to bound how many tropical segments are needed to follow the tropical central path.
--
--   **Formalization Note** $\mathbb T$ is `WithBot ℝ`. "Polygonal curve" is encoded through the monotone parametrization $\mu\mapsto u\oplus(\mu\odot v)$ of the proof: on the $k$-th piece the curve moves by $(\mu'-\mu)e^{K_k}$, coordinates equal to $-\infty$ staying $-\infty$. When some $u_i=-\infty<v_i$, the first piece is unbounded ($c_0=-\infty$) and the point $u$ itself is its limit; this is why $u$ is added separately. Requiring each $K_k$ non-empty (a segment has a non-zero direction) matches the proof's chain $K_0=\emptyset\subsetneq K_1\subsetneq\cdots$.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 10, Lemma 5

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_TropicalSegment

namespace LogBarrierIPM.Iterations

/-- Lemma 5 (p. 10). Let `u ≤ v` in `𝕋^d`. Then `tsegm(u, v)` is `{u}` together with the curve
`μ ↦ u ⊕ (μ ⊙ v)`, `μ ∈ (−∞, 0]`, which runs from `u` to `v` (its value at `μ = 0` is `v`), and this
curve is polygonal: there are `ℓ ≤ d`, non-empty sets `K_1 ⊊ ⋯ ⊊ K_ℓ ⊆ [d]` and breakpoints
`c_0 < c_1 < ⋯ < c_ℓ = 0` in `ℝ ∪ {−∞}` such that the curve stays at `u` for `μ ≤ c_0` and, on
`[c_{k−1}, c_k]`, moves along the direction vector `e^{K_k}` (the 0/1 indicator of `K_k`). -/
theorem lemma_5 {d : ℕ} (u v : Fin d → WithBot ℝ) (huv : u ≤ v) :
    tsegm u v = insert u (Set.range fun mu : Set.Iic (0 : ℝ) => tsegParam u v mu) ∧
    ∃ (ℓ : ℕ) (K : Fin ℓ → Finset (Fin d)) (c : Fin (ℓ + 1) → WithBot ℝ),
      ℓ ≤ d ∧ (∀ k, (K k).Nonempty) ∧ StrictMono K ∧ StrictMono c ∧
      c (Fin.last ℓ) = 0 ∧
      (∀ mu : ℝ, (mu : WithBot ℝ) ≤ c 0 → tsegParam u v mu = u) ∧
      ∀ (k : Fin ℓ) (mu mu' : ℝ), c k.castSucc ≤ (mu : WithBot ℝ) → mu ≤ mu' →
        (mu' : WithBot ℝ) ≤ c k.succ →
        ∀ i, tsegParam u v mu' i =
          tsegParam u v mu i + (((mu' - mu) * (if i ∈ K k then 1 else 0) : ℝ) : WithBot ℝ) := by sorry

end LogBarrierIPM.Iterations
