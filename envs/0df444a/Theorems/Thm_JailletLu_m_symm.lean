-- Prove2me | Theorems.Thm_JailletLu_m_symm
-- name    : JailletLu.m_symm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:28:20.958305+00:00
-- url     : https://prove2.me/theorems/b7c0130b-3be2-48f2-9ca8-14d0206a1e72
-- title:
--   §5.3: symmetry of the list numbers, $m^i_{b,c}=m^i_{c,b}$ and $m_{b,c}=m_{c,b}$
-- statement:
--   **Setting.** Let $A$ (advertisers) and $I$ (impression types) be finite sets, $E\subseteq A\times I$ the edges of the bipartite graph ($a\sim i$ when $(a,i)\in E$), $r_i\le 1$ the arrival rate of type $i$ (the standing assumption of §5), and $n$ the number of requests. Let $f=(f_{a,i})$ be a feasible point of LP (4), extended by the dummy advertiser $a_d$ with $f_{a_d,i}=r_i-\sum_{a}f_{a,i}$ and the convention $f_{a_d}=1$, and write $f_a=\sum_{i\sim a}f_{a,i}$. Fix, for every type $i$, any order $a_1,\dots,a_k$ of the advertisers interested in $i$ (the dummy included). The list numbers $m^i_{b,c}$ and $m_{b,c}=\sum_i m^i_{b,c}$ ($b,c\in A^*=A\cup\{a_d\}$) are those of the §5.3 construction, and for $a\in A$: $A^*_a=A^*\setminus\{a\}$, $\beta_a=\max_{a_1\in A^*_a}m_{a,a_1}$, $s_a=\sum_{a_1\in A^*_a}m_{a,a_1}$.
--
--   Then for every type $i$ and all $b,c\in A^*$,
--   $$
--   m^i_{b,c}=m^i_{c,b}\qquad\text{and}\qquad m_{b,c}=m_{c,b}.
--   $$
--   A list $\langle b,c\rangle$ is as likely as the reversed list $\langle c,b\rangle$. This symmetry is what lets §5.4 identify $\beta_a=\max_{a_1}m_{a,a_1}$ with the largest $m_{a_1,a}$.
--
--   Differences from the source:
--   - reading: the order a_1, …, a_k of the advertisers interested in i is not fixed → every admissible order: a duplicate-free list of exactly the interested advertisers, dummy included; reason: the paper fixes no order; the statement holds for every one
--   - reading: x ± r_i/2 ∈ [Σ_{l<k} f_{a_l,i}, Σ_{l≤k} f_{a_l,i}] → rot(x) = x + r_i/2 if x < r_i/2, else x − r_i/2, with closed intervals; reason: for x ∈ [0, r_i] this is the one of x ± r_i/2 lying in [0, r_i] (both only at x = r_i/2); interval endpoints have measure 0
--   - encoding: m^i_{b,c}, the expected number of requests of type i whose list is ⟨b, c⟩ → Lebesgue measure of {x ∈ [0, r_i] : x ∈ J_i(b), rot(x) ∈ J_i(c)}; reason: n requests, type i with probability r_i/n, x uniform on [0, r_i]: n · (r_i/n) · |·|/r_i = |·|; same values, the probability space is not built
--   - generalization: f the solution of LP (4) used by the algorithm, with Σ_i r_i = n → f any feasible point of LP (4); Σ_i r_i = n not assumed; reason: optimality and the normalization are never used; the paper's f is feasible, so the statement specializes to it
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13 (unnumbered)

import Mathlib
import Definitions.Def_JailletLu_LP4Feasible
import Definitions.Def_JailletLu_IsAdmissibleOrder
import Definitions.Def_JailletLu_mi
import Definitions.Def_JailletLu_m

namespace JailletLu

/-- **Symmetry of the list numbers** (unnumbered).
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13: "From the construction of the lists, we have m^i_{a_j,a_k} = m^i_{a_k,a_j}." and
"Furthermore, because m^i_{a_j,a_k} = m^i_{a_k,a_j}, we have m_{a_j,a_k} = m_{a_k,a_j}."

Setting (§5, p. 12 and §5.3, p. 13): `r_i ≤ 1` for every type (the standing assumption of §5), `f`
feasible for LP (4) with parameter `n`, and an admissible order of the interested advertisers for
every type (any order: the paper fixes none). The list numbers are those of the §5.3 construction.
Conclusion: `m^i_{b,c} = m^i_{c,b}` for every type `i` and all `b, c ∈ A*`, and `m_{b,c} = m_{c,b}`. -/
theorem m_symm {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]
    (E : Set (A × I)) (r : I → ℝ) (hr : ∀ i, r i ≤ 1) (n : ℕ) (f : A → I → ℝ)
    (hf : LP4Feasible E r n f) (ord : I → List (Option A)) (hord : IsAdmissibleOrder E ord) :
    (∀ i (b c : Option A), mi r f ord i b c = mi r f ord i c b) ∧
      (∀ b c : Option A, m r f ord b c = m r f ord c b) := by sorry

end JailletLu
