-- Prove2me | Theorems.Thm_JailletLu_claim4_constraints
-- name    : JailletLu.claim4_constraints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:29:12.983379+00:00
-- url     : https://prove2.me/theorems/1a0a98ba-ac91-4168-8418-d1f5667b32b0
-- title:
--   §5.4: the constraints of Claim 4 hold, $1\ge f_a\ge s_a\ge\beta_a\ge0$ and $f_a-s_a\le 1-\ln2+1/n$
-- statement:
--   **Setting.** Let $A$ (advertisers) and $I$ (impression types) be finite sets, $E\subseteq A\times I$ the edges of the bipartite graph ($a\sim i$ when $(a,i)\in E$), $r_i\le 1$ the arrival rate of type $i$ (the standing assumption of §5), and $n$ the number of requests. Let $f=(f_{a,i})$ be a feasible point of LP (4), extended by the dummy advertiser $a_d$ with $f_{a_d,i}=r_i-\sum_{a}f_{a,i}$ and the convention $f_{a_d}=1$, and write $f_a=\sum_{i\sim a}f_{a,i}$. Fix, for every type $i$, any order $a_1,\dots,a_k$ of the advertisers interested in $i$ (the dummy included). The list numbers $m^i_{b,c}$ and $m_{b,c}=\sum_i m^i_{b,c}$ ($b,c\in A^*=A\cup\{a_d\}$) are those of the §5.3 construction, and for $a\in A$: $A^*_a=A^*\setminus\{a\}$, $\beta_a=\max_{a_1\in A^*_a}m_{a,a_1}$, $s_a=\sum_{a_1\in A^*_a}m_{a,a_1}$.
--
--   Then for every advertiser $a\in A$:
--   1. $1\ge f_a\ge s_a\ge\beta_a\ge 0$;
--   2. $f_a-s_a=m_{a,a}$, the expected number of singleton lists $\langle a\rangle$;
--   3. $m^i_{a,a}=(2f_{a,i}-r_i)^+$ for every type $i$;
--   4. $$f_a-s_a=\sum_{i\sim a}(2f_{a,i}-r_i)^+\le(1-\ln 2)+\frac1n;$$
--   5. $m_{b,a}\le f_b$ for every $b\in A^*_a$ (with $f_{a_d}=1$).
--
--   Items 1 and 4 are exactly the constraints under which Claim 4 bounds $R(f_a,\beta_a,s_a)$; they are consequences of the construction, not assumptions.
--
--   Differences from the source:
--   - reading: the order a_1, …, a_k of the advertisers interested in i is not fixed → every admissible order: a duplicate-free list of exactly the interested advertisers, dummy included; reason: the paper fixes no order; the statement holds for every one
--   - reading: x ± r_i/2 ∈ [Σ_{l<k} f_{a_l,i}, Σ_{l≤k} f_{a_l,i}] → rot(x) = x + r_i/2 if x < r_i/2, else x − r_i/2, with closed intervals; reason: for x ∈ [0, r_i] this is the one of x ± r_i/2 lying in [0, r_i] (both only at x = r_i/2); interval endpoints have measure 0
--   - encoding: m^i_{b,c}, the expected number of requests of type i whose list is ⟨b, c⟩ → Lebesgue measure of {x ∈ [0, r_i] : x ∈ J_i(b), rot(x) ∈ J_i(c)}; reason: n requests, type i with probability r_i/n, x uniform on [0, r_i]: n · (r_i/n) · |·|/r_i = |·|; same values, the probability space is not built
--   - generalization: f the solution of LP (4) used by the algorithm, with Σ_i r_i = n → f any feasible point of LP (4); Σ_i r_i = n not assumed; reason: optimality and the normalization are never used; the paper's f is feasible, so the statement specializes to it
--   - generalization: the paragraph states f_a ≥ s_a ≥ β_a, f_a − s_a = expected number of singletons ⟨a⟩ = Σ_{i∼a}(2f_{a,i} − r_i)^+ ≤ (1 − ln 2) + 1/n → the same, plus f_a ≤ 1, β_a ≥ 0 (the rest of Claim 4's constraint 1 ≥ f_a ≥ s_a ≥ β_a ≥ 0) and m_{b,a} ≤ f_b for b ∈ A*_a; reason: extra conclusions that follow from LP (4) and the definitions on p. 13 and are used on p. 15; the paragraph's statements are all included
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 16, paragraph before Claim 4 (unnumbered)

import Mathlib
import Definitions.Def_JailletLu_LP4Feasible
import Definitions.Def_JailletLu_IsAdmissibleOrder
import Definitions.Def_JailletLu_fTot
import Definitions.Def_JailletLu_fStar
import Definitions.Def_JailletLu_mi
import Definitions.Def_JailletLu_m
import Definitions.Def_JailletLu_Astar
import Definitions.Def_JailletLu_beta
import Definitions.Def_JailletLu_sA

namespace JailletLu

/-- **The constraints of Claim 4 hold in the model** (unnumbered).
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 16, paragraph before Claim 4: "From the definitions of f_a, β_a, and s_a, we have
f_a ≥ s_a ≥ β_a, and f_a − s_a is the expected number of lists that are singletons ⟨a⟩. From the
construction of lists, the expected number of singletons ⟨a⟩ associated with impressions of types i
is (2f_{a,i} − r_i)^+. Thus, f_a − s_a = Σ_{i∼a}(2f_{a,i} − r_i)^+ ≤ (1 − ln 2) + 1/n."

Setting (§5, p. 12 and §5.3, p. 13): `r_i ≤ 1` for every type (the standing assumption of §5), `f`
feasible for LP (4) with parameter `n`, and an admissible order of the interested advertisers for
every type (any order: the paper fixes none). The list numbers are those of the §5.3 construction.
Conclusion, for every advertiser `a`:
1. `0 ≤ β_a ≤ s_a ≤ f_a ≤ 1` (the constraint `1 ≥ f_a ≥ s_a ≥ β_a ≥ 0` of Claim 4);
2. `f_a − s_a = m_{a,a}`, the expected number of singleton lists `⟨a⟩`;
3. `m^i_{a,a} = (2 f_{a,i} − r_i)^+` for every type `i`;
4. `f_a − s_a = Σ_i (2 f_{a,i} − r_i)^+ ≤ (1 − ln 2) + 1/n`;
5. `m_{b,a} ≤ f_b` for every `b ∈ A*_a` (with `f_{a_d} = 1`). -/
theorem claim4_constraints {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]
    (E : Set (A × I)) (r : I → ℝ) (hr : ∀ i, r i ≤ 1) (n : ℕ) (f : A → I → ℝ)
    (hf : LP4Feasible E r n f) (ord : I → List (Option A)) (hord : IsAdmissibleOrder E ord) (a : A) :
    0 ≤ beta r f ord a ∧ beta r f ord a ≤ sA r f ord a ∧ sA r f ord a ≤ fTot f a ∧
      fTot f a ≤ 1 ∧
      fTot f a - sA r f ord a = m r f ord (some a) (some a) ∧
      (∀ i, mi r f ord i (some a) (some a) = max (2 * f a i - r i) 0) ∧
      fTot f a - sA r f ord a = ∑ i, max (2 * f a i - r i) 0 ∧
      fTot f a - sA r f ord a ≤ (1 - Real.log 2) + 1 / (n : ℝ) ∧
      (∀ b ∈ Astar a, m r f ord b (some a) ≤ fStar f b) := by sorry

end JailletLu
