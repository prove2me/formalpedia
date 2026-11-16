-- Prove2me | Theorems.Thm_MeanBudgetXC_Supplement_theorem_6_1
-- name    : MeanBudgetXC.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:16:36.065717+00:00
-- url     : https://prove2.me/theorems/8c78ee2d-bf55-4dde-91a3-1844c0b087c9
-- title:
--   Theorem 6.1 — aggregate moments and disposal: $K^{\mathrm{mom}}_{N,d,2}=\Delta_M$, and $2^{\Theta_{a,\theta}(N)}$ / $2^{cN^\kappa}$ lower bounds for $a\ge3$
-- statement:
--   Write $W(q)=\sum_{i<j}q_{ij}$, $M_a=\operatorname{conv}\{(j,\binom j2): j=0,\dots,a\}$, and let $K^{\mathrm{mom}}_{N,d,a}$ be the pair projection of consistent local laws of context size $d$ and activity $a$ after imposing $(\sum_ip_i,W(q))\in M_a$. For a set $A$ of pair arrays, $D(A)=\{x\ge0:\exists q\in A,\ x\le q\}$ is its downward closure (free disposal), and $\Delta_M=\{q\ge0:W(q)\le1\}$. Capped values $V_A(u)$, common LPs and their errors are as in Section 1.3; $\Gamma_L=\{j/L:j=0,\dots,L\}$.
--
--   1. For $3\le d\le N$,
--   $$K^{\mathrm{mom}}_{N,d,2}=D(K^{\mathrm{mom}}_{N,d,2})=\Delta_M.$$
--   2. For every fixed integer $a\ge3$ and $0<\theta<1$, for all sufficiently large $N$ and $d=\lfloor\theta N\rfloor$,
--   $$\mathrm{xc}\big(D(K^{\mathrm{mom}}_{N,d,a})\big)=2^{\Theta_{a,\theta}(N)}.$$
--   3. There is an absolute $\kappa>0$ (the exponent of Theorem 5.2) and there are constants $e,c>0$, depending on $a,\theta$, such that any common LP whose capped sets are nonempty at every cap in $[0,1]^M$ and whose capacity values approximate $V_{D(K^{\mathrm{mom}}_{N,d,a})}$ within total error $e$ on every cap in $[0,1]^M$ requires at least $2^{cN^\kappa}$ inequalities.
--   4. The same holds on a grid $\Gamma^M_{L_N}$ with $L_N=O_{a,\theta}(N^2)$, hence $O_{a,\theta}(\log N)$ bits per coordinate: the hypotheses of item 3 are then required only at caps in $\Gamma^M_{L_N}$.
--
--   Strengthening the mean budget by every valid aggregate inequality removes all non-global points at activity two, but not at higher activity, even with free disposal.
--
--   **Formalization Note** Upper bounds are stated as the existence of a formulation of the given size, never as a bound on an infimum.
--
--   Differences from the source:
--   - encoding: the vertex set $[N]$ → `Fin N`; reason: the same set, indexed from zero
--   - encoding: a common LP (base formulation) with $s$ inequalities and output polyhedron $K$ → `IsEFOfSize K s` (platform); reason: the paper's counting convention (p.4, App. A.1): inequalities counted, equations and auxiliary variables free, real coefficients, unbounded lifts allowed
--   - encoding: $V_A(u)=\max\{1^{\mathsf T}q: q\in A,\ 0\le q\le u\}$ → `capValue A u`, the supremum of $\sum_e q_e$ over the capped set; reason: the capped set is nonempty and lies in the box $[0,u]$, and $A$ is a polyhedron or a compact body, so the supremum is attained and equals the maximum
--   - encoding: nonempty capped feasible sets and finite values → nonempty capped sets only; reason: the capped set lies in the box $[0,u]$, so the value is always finite; the finiteness hypothesis excludes nothing
--   - reading: $\kappa$ is the exponent of Theorem 5.2 → an absolute $\kappa>0$ quantified first, before every other constant; reason: each statement is standalone; Theorem 5.2 fixes $\kappa$ only as an absolute positive constant
--   - reading: $\mathrm{xc}(D(K^{\mathrm{mom}}_{N,d,a}))=2^{\Theta_{a,\theta}(N)}$ for all sufficiently large $N$ → constants $c_1,c_2>0$ and a threshold depending on $a,\theta$, with $2^{c_1N}\le\mathrm{xc}$ and a formulation (`IsEFOfSize`) of size at most $2^{c_2N}$; reason: the subscripts fix the dependence; an exhibited formulation implies the upper bound and avoids the infimum's junk value
--   - reading: "the same holds on a grid $\Gamma^M_{L_N}$ with $L_N=O_{a,\theta}(N^2)$, and $O_{a,\theta}(\log N)$ bits per coordinate" → a constant $C_{\mathrm{grid}}$ depending on $a,\theta$ and, for each large $N$, an integer $1\le L_N\le C_{\mathrm{grid}}N^2$ for which the lower bound holds with the hypotheses imposed only on caps in $\Gamma^M_{L_N}$; reason: the theorem asserts such a grid exists (Section 6.5 constructs one); the bit bound follows from $L_N\le C_{\mathrm{grid}}N^2$
--   - encoding: "for all sufficiently large $N$" for item 2 and for items 3–4 → one threshold for items 2–4; reason: each clause is monotone in the threshold
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Theorem 6.1, pp.29–30

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_MeanBudgetXC_downClosure
import Definitions.Def_MeanBudgetXC_Supplement_momentBody
import Definitions.Def_MeanBudgetXC_Supplement_simplexBody
import Definitions.Def_LinfContractionFP_unitCube
import Definitions.Def_MeanBudgetXC_Supplement_IsGridCap
import Definitions.Def_MeanBudgetXC_Supplement_capValue

namespace MeanBudgetXC.Supplement

open ExtensionComplexity.TSP

/-- **Theorem 6.1** (The boundary of aggregate strengthening) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Theorem 6.1, pp.29–30). For `3 ≤ d ≤ N`,
`K^mom_{N,d,2} = D(K^mom_{N,d,2}) = Δ_M`. For every fixed integer `a ≥ 3` and `0 < θ < 1`, for all
sufficiently large `N` and `d = ⌊θN⌋`, `xc(D(K^mom_{N,d,a})) = 2^{Θ_{a,θ}(N)}`. There are constants
`e, c > 0`, depending on `a, θ`, such that any common LP for the retained vectors whose capacity
values approximate `V_{D(K^mom_{N,d,a})}` within total error `e` on every cap in `[0, 1]^M` requires
at least `2^{cN^κ}` inequalities. The same holds on a grid `Γ^M_{L_N}` with
`Γ_{L_N} = {j/L_N : j = 0, …, L_N}`, `L_N = O_{a,θ}(N²)`, and `O_{a,θ}(log N)` bits per coordinate.
All queried caps must have nonempty feasible sets and finite values.

**Formalization Note** `K^mom_{N,d,a} = momentBody (Fin N) d a`, `D(A) = downClosure A` (published),
`Δ_M = simplexBody`. `xc = 2^{Θ_{a,θ}(N)}` is read as constants `c₁, c₂ > 0` and a threshold
depending on `a, θ`, with `2^{c₁N} ≤ xc` and a formulation of size at most `2^{c₂N}` (stated as the
existence of a formulation, never as a bound on the infimum). `κ` is the absolute exponent of
Theorem 5.2, chosen first. The common LP is `IsEFOfSize K s` with `K` arbitrary; finite values are
automatic, so only nonemptiness is assumed. `L_N = O_{a,θ}(N²)` is read as a constant `C_grid`
depending on `a, θ` and, for each large `N`, an integer `1 ≤ L_N ≤ C_grid N²` for which the lower
bound holds when the hypotheses are imposed only on caps in `Γ^M_{L_N}`; the
`O_{a,θ}(log N)` bits per coordinate follow from `L_N ≤ C_grid N²`. One threshold serves the exact
and approximate clauses. -/
theorem theorem_6_1 :
    (∀ N d : ℕ, 3 ≤ d → d ≤ N →
      momentBody (Fin N) d 2 = downClosure (momentBody (Fin N) d 2) ∧
        downClosure (momentBody (Fin N) d 2) = simplexBody (Pair (Fin N))) ∧
    ∃ κ : ℝ, 0 < κ ∧ ∀ a : ℕ, 3 ≤ a → ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ c₁ c₂ e c Cgrid : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < e ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ((2 : ℝ) ^ (c₁ * N) ≤
            extensionComplexity (downClosure (momentBody (Fin N) ⌊θ * N⌋₊ a)) ∧
          ∃ r : ℕ, IsEFOfSize (downClosure (momentBody (Fin N) ⌊θ * N⌋₊ a)) r ∧
            (r : ℝ) ≤ (2 : ℝ) ^ (c₂ * N)) ∧
        (∀ (K : Set (Pair (Fin N) → ℝ)) (s : ℕ), IsEFOfSize K s →
          (∀ u ∈ LinfContractionFP.unitCube (Pair (Fin N)), (cappedSet K u).Nonempty) →
          (∀ u ∈ LinfContractionFP.unitCube (Pair (Fin N)),
            |capValue K u - capValue (downClosure (momentBody (Fin N) ⌊θ * N⌋₊ a)) u| ≤ e) →
          (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ s) ∧
        ∃ L : ℕ, 1 ≤ L ∧ (L : ℝ) ≤ Cgrid * (N : ℝ) ^ 2 ∧
          ∀ (K : Set (Pair (Fin N) → ℝ)) (s : ℕ), IsEFOfSize K s →
            (∀ u : Pair (Fin N) → ℝ, IsGridCap L u → (cappedSet K u).Nonempty) →
            (∀ u : Pair (Fin N) → ℝ, IsGridCap L u →
              |capValue K u - capValue (downClosure (momentBody (Fin N) ⌊θ * N⌋₊ a)) u| ≤ e) →
            (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ s := by sorry

end MeanBudgetXC.Supplement
