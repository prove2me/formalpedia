-- Prove2me | Theorems.Thm_JailletLu_concavity_sum_ge
-- name    : JailletLu.concavity_sum_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:31:52.884858+00:00
-- url     : https://prove2.me/theorems/201af027-f8a7-4d57-b600-83673b4ddf8d
-- title:
--   §5.4: $\sum_{a_1\in A^*_a}g(f_a,m_{a,a_1})\ge (s_a/\beta_a)\,g(f_a,\beta_a)$
-- statement:
--   **Setting.** Let $A$ (advertisers) and $I$ (impression types) be finite sets, $E\subseteq A\times I$ the edges of the bipartite graph ($a\sim i$ when $(a,i)\in E$), $r_i\le 1$ the arrival rate of type $i$ (the standing assumption of §5), and $n$ the number of requests. Let $f=(f_{a,i})$ be a feasible point of LP (4), extended by the dummy advertiser $a_d$ with $f_{a_d,i}=r_i-\sum_{a}f_{a,i}$ and the convention $f_{a_d}=1$, and write $f_a=\sum_{i\sim a}f_{a,i}$. Fix, for every type $i$, any order $a_1,\dots,a_k$ of the advertisers interested in $i$ (the dummy included). The list numbers $m^i_{b,c}$ and $m_{b,c}=\sum_i m^i_{b,c}$ ($b,c\in A^*=A\cup\{a_d\}$) are those of the §5.3 construction, and for $a\in A$: $A^*_a=A^*\setminus\{a\}$, $\beta_a=\max_{a_1\in A^*_a}m_{a,a_1}$, $s_a=\sum_{a_1\in A^*_a}m_{a,a_1}$.
--
--   Then for every advertiser $a\in A$,
--   $$
--   \sum_{a_1\in A^*_a}g(f_a,m_{a,a_1})\ \ge\ \frac{s_a}{\beta_a}\,g(f_a,\beta_a).
--   $$
--   It follows from the concavity of $g$ in its second argument and $g(f_a,0)=0$, and replaces the first sum of the third line by a function of $f_a,\beta_a,s_a$.
--
--   **Formalization Note** When $\beta_a=0$, every $m_{a,a_1}$ vanishes and both sides are $0$ (Lean reads $s/0$ as $0$).
--
--   Differences from the source:
--   - reading: the order a_1, …, a_k of the advertisers interested in i is not fixed → every admissible order: a duplicate-free list of exactly the interested advertisers, dummy included; reason: the paper fixes no order; the statement holds for every one
--   - reading: x ± r_i/2 ∈ [Σ_{l<k} f_{a_l,i}, Σ_{l≤k} f_{a_l,i}] → rot(x) = x + r_i/2 if x < r_i/2, else x − r_i/2, with closed intervals; reason: for x ∈ [0, r_i] this is the one of x ± r_i/2 lying in [0, r_i] (both only at x = r_i/2); interval endpoints have measure 0
--   - encoding: m^i_{b,c}, the expected number of requests of type i whose list is ⟨b, c⟩ → Lebesgue measure of {x ∈ [0, r_i] : x ∈ J_i(b), rot(x) ∈ J_i(c)}; reason: n requests, type i with probability r_i/n, x uniform on [0, r_i]: n · (r_i/n) · |·|/r_i = |·|; same values, the probability space is not built
--   - generalization: f the solution of LP (4) used by the algorithm, with Σ_i r_i = n → f any feasible point of LP (4); Σ_i r_i = n not assumed; reason: optimality and the normalization are never used; the paper's f is feasible, so the statement specializes to it
--   - encoding: s_a/β_a, undefined at β_a = 0 → Lean's s/0 = 0; reason: at β_a = 0 all m_{a,a1} vanish and both sides are 0; no instance with β_a > 0 changes
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15 (unnumbered)

import Mathlib
import Definitions.Def_JailletLu_LP4Feasible
import Definitions.Def_JailletLu_IsAdmissibleOrder
import Definitions.Def_JailletLu_fTot
import Definitions.Def_JailletLu_fStar
import Definitions.Def_JailletLu_m
import Definitions.Def_JailletLu_Astar
import Definitions.Def_JailletLu_beta
import Definitions.Def_JailletLu_sA
import Definitions.Def_JailletLu_g

namespace JailletLu

/-- **The concavity bound** (unnumbered).
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15: "Furthermore, because g is concave in the second argument and g(f_a, 0) = 0,
Σ_{a1∈A*_a} g(f_a, m_{a,a1}) ≥ Σ_{a1∈A*_a} (m_{a,a1}/β_a) g(f_a, β_a) = (s_a/β_a) g(f_a, β_a)."

Setting (§5, p. 12 and §5.3, p. 13): `r_i ≤ 1` for every type (the standing assumption of §5), `f`
feasible for LP (4) with parameter `n`, and an admissible order of the interested advertisers for
every type (any order: the paper fixes none). The list numbers are those of the §5.3 construction.
Conclusion, for every advertiser `a`: `Σ_{b ∈ A*_a} g(f_a, m_{a,b}) ≥ (s_a/β_a) g(f_a, β_a)`.

**Formalization Note.** At `β_a = 0` every `m_{a,b}` (`b ∈ A*_a`) is `0`, both sides are `0` (Lean's
`s/0 = 0`), and the statement holds; no hypothesis `β_a > 0` is added. The intermediate sum
`Σ (m_{a,a1}/β_a) g(f_a, β_a)` equals the right side by the definition of `s_a` and is not stated. -/
theorem concavity_sum_ge {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]
    (E : Set (A × I)) (r : I → ℝ) (hr : ∀ i, r i ≤ 1) (n : ℕ) (f : A → I → ℝ)
    (hf : LP4Feasible E r n f) (ord : I → List (Option A)) (hord : IsAdmissibleOrder E ord) (a : A) :
    sA r f ord a / beta r f ord a * g (fTot f a) (beta r f ord a) ≤
      ∑ b ∈ Astar a, g (fTot f a) (m r f ord (some a) b) := by sorry

end JailletLu
