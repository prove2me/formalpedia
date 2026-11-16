-- Prove2me | Theorems.Thm_FourBlockIP350_Main_Supplement_periodic_midpoint_convex
-- name    : FourBlockIP350.Main.Supplement.periodic_midpoint_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:09:01.683747+00:00
-- url     : https://prove2.me/theorems/f282ac3a-ad75-40d9-9251-39454352aadd
-- title:
--   Lemma B.5 — Periodic midpoint convexity of $H_{K,r}$
-- statement:
--   Let $I$ be a 4-block instance with $k,n\ge1$, local blocks bounded by $\bar\Delta\ge1$, and finite integral bounds with nonempty intervals, and let $\Phi=\sum_j\phi_j$ be separable convex with every $\phi_j:\mathbb R\to\mathbb R$ convex. For real $K$ let
--   $$F_K(x)=\min_{y\in Y}\{\Phi(x,y)+K\|b-Zx-Ey\|_1\},\qquad x\in\mathbb Z^k .$$
--   Let $N$ be a positive integer with the uniform dilation property of Proposition 2.6 for generalized $n$-fold matrices with blocks of size $2k$ and entries bounded by $\bar\Delta$; this covers the matrix $Q=[E\ I]$ with the residual variables grouped into bricks. Then for every real $K>0$ and every $r\in\{0,\dots,N-1\}^k$ the function
--   $$H_{K,r}(v)=F_K(r+Nv),\qquad v\in\mathbb Z^k,$$
--   is everywhere finite and midpoint-convex: $2H_{K,r}(w)\le H_{K,r}(a')+H_{K,r}(a'')$ whenever $a'+a''=2w$ with $a',a'',w\in\mathbb Z^k$.
--
--   This is the structural input for optimizing over the global variables one residue class at a time, for an arbitrary penalty coefficient $K$.
--
--   **Formalization Note** Finiteness is a conclusion at every $v$; the midpoint inequality is stated for the real value of $F_K$.
--
--   Differences from the source:
--   - generalization: N is the positive integer provided by Proposition 2.6 for Q = [E I] → every N > 0 with UniformDilation (2*k) Δbar N; reason: the N of Proposition 2.6 (published uniform_idp, applied at block size 2k, the brick width of Q stated on p. 7) has this property, so the statement specializes to the source's
--   - encoding: Δbar is the largest absolute entry of the blocks B, D → any Δ ≥ 1 bounding those entries; reason: Δbar ≥ 1 is a standing assumption (p. 2); the statement at Δ = Δbar is the source's
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 24, Lemma B.5, with (B.5) on p. 23 and the standing assumptions of §B.1, p. 21

import Mathlib
import Definitions.Def_FourBlockIP350_Main_Supplement_SeparableIP
import Definitions.Def_FourBlockIP350_Main_Decomposition

open scoped BigOperators

namespace FourBlockIP350.Main.Supplement

open FourBlockIP350.Main

/-- Lemma B.5, p. 24: for every real `K > 0` and residue `r ∈ {0, …, N−1}^k`,
`H_{K,r}(v) = F_K(r + N v)` is finite at every `v ∈ ℤ^k` and midpoint-convex. Here `N` is a
positive period with the uniform dilation property of Proposition 2.6 for block size `2k`,
the size of the blocks of `Q = [E I]`. -/
theorem periodic_midpoint_convex {k n Δ N : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hΔ : 0 < Δ) (hN : 0 < N) (hdil : UniformDilation (2 * k) Δ N)
    (I : FourBlock k n) (hI : I.localPart.Bounded Δ) (hbox : GoodBox I)
    (φ : BlockCol k n → ℝ → ℝ) (hφ : SeparableConvex φ)
    (K : ℝ) (hK : 0 < K) (r : ZVec k) (hr : IsResidue N r) :
    (∀ v : ZVec k, ∃ t : ℝ, FK I φ K (r + (N : ℤ) • v) = (t : EReal)) ∧
      MidpointConvex (HK I φ K N r) := by sorry

end FourBlockIP350.Main.Supplement
