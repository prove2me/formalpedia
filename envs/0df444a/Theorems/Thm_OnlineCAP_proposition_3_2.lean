-- Prove2me | Theorems.Thm_OnlineCAP_proposition_3_2
-- name    : OnlineCAP.proposition_3_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T07:24:28.772838+00:00
-- url     : https://prove2.me/theorems/ff15483b-b0b8-4f6d-9057-21af5c678e32
-- title:
--   Proposition 3.2 — a link crosses the cut [a, b] iff its point lies in R_L(a, b) ∪ R_T(a, b)
-- statement:
--   Number the vertices of the cycle $v_0,v_1,\dots,v_{n-1}$ in cyclic order and let $C=[a,b]=\{v_a,v_{a+1},\dots,v_b\}$ with $1\le a\le b\le n-1$ (the minimum cuts of the cycle that avoid $v_0$). For a link $\ell=\{v_i,v_j\}$ with $i<j\le n-1$ and its point $p_\ell=(i,j)$,
--   $$\ell\text{ has exactly one end in } C\iff p_\ell\in R_L(a,b)\cup R_T(a,b)=\big((-\infty,a-1]\times[a,b]\big)\cup\big([a,b]\times[b+1,\infty)\big).$$
--
--   This turns the cut requests of OCycAP into TL shapes and links into points, which is the reduction behind Theorem 1.10.
--
--   Differences from the source:
--   - encoding: the minimum cut C = [a, b] = {v_a, …, v_b}, 1 ≤ a ≤ b ≤ n − 1 → the vertex set {v ∈ Fin n : a ≤ v ≤ b} for naturals 1 ≤ a ≤ b ≤ n − 1; reason: these arcs are exactly the minimum cuts of the cycle avoiding v₀ (§3.1, pp.10–11); same instances
--   - encoding: p_ℓ = (i, j) ∈ ℤ² and RL, RT ⊆ ℝ² → the point ((i : ℝ), (j : ℝ)) ∈ ℝ²; reason: the paper's rectangles are subsets of ℝ² (p.11); the cast is the inclusion ℤ² ⊆ ℝ²
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Proposition 3.2, p.11

import Mathlib
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_RL
import Definitions.Def_OnlineCAP_RT

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Proposition 3.2 (links as points in a TL shape).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Proposition 3.2, p.11 (PDF p.11):
"A link ℓ = (vi, vj) with i < j crosses the minimum cut C = [a, b] if and only if
pℓ = (i, j) ∈ RL(a, b) ∪ RT(a, b)."

For vertices `v_i, v_j` of `Fin n` with `i < j < n` and the arc `C = [a, b] = {v_a, …, v_b}`,
`1 ≤ a ≤ b ≤ n − 1`: the link `{v_i, v_j}` has exactly one end in `C` iff
`(i, j) ∈ (−∞, a − 1] × [a, b] ∪ [a, b] × [b + 1, ∞)`.

**Formalization Note.** The minimum cuts of the cycle `v₀ v₁ ⋯ v_{n−1} v₀` that avoid `v₀` are
exactly these arcs (§3.1, pp.10–11), so the statement is quantified over the arcs. -/
theorem proposition_3_2 (n i j a b : ℕ) (hij : i < j) (hjn : j < n) (ha : 1 ≤ a) (hab : a ≤ b)
    (hbn : b ≤ n - 1) :
    crosses s((⟨i, by omega⟩ : Fin n), (⟨j, hjn⟩ : Fin n))
        (Finset.univ.filter (fun v : Fin n => a ≤ v.val ∧ v.val ≤ b)) ↔
      ((i : ℝ), (j : ℝ)) ∈ RL a b ∪ RT a b := by sorry

end OnlineCAP
