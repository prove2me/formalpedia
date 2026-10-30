-- Prove2me | Theorems.Thm_NestedLogitNBR_feasible7_feasibleFull
-- name    : NestedLogitNBR.feasible7_feasibleFull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:42:53.993751+00:00
-- url     : https://prove2.me/theorems/03293a56-46fb-4f0b-ba34-3927020cbcb4
-- title:
--   Problem (3) is a relaxation of problem (7)
-- statement:
--   There are $m$ nests $M=\{1,\dots,m\}$, each offering products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}\ge 0$, and the products of every nest are ordered so that $r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$. Nest $i$ has a dissimilarity parameter $\gamma_i\ge 0$, and $v_0\ge 0$ is the preference weight of choosing no nest. As in Section 4 of the paper the no-purchase weights inside the nests are $v_{i0}=0$, so $V_i(S)=\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$. The nested-by-revenue assortments are $N_{ij}=\{1,\dots,j\}$ for $j\in N_+=\{0,1,\dots,n\}$, with $N_{i0}=\emptyset$.
--
--   Every feasible solution of the fractional program (7) is feasible for the full assortment linear program (3): if $v_0x\ge\sum_i y_i$ and
--
--   $$
--   y_i\ \ge\ \Big(\sum_{j\in N}v_{ij}z_{j}\Big)^{\gamma_i}\left[\frac{\sum_{j\in N}r_{ij}v_{ij}z_{j}}{\sum_{j\in N}v_{ij}z_{j}}-x\right]\quad\text{for all } z\in[0,1]^n,\ i\in M,
--   $$
--
--   then $y_i\ge V_i(S)^{\gamma_i}(R_i(S)-x)$ for every $S\subseteq N$. The proof of Theorem 7 shows feasibility for (7), which this step transfers to (3).
--
--   Differences from the source:
--   - generalization: the standing assumptions of §1 and §4 (v_ij ≥ 0, r_i1 ≥ … ≥ r_in, γ_i ≥ 0, γ_i > 1 for some i) → no assumption on the data; reason: the implication holds for all data; every instance of the model is covered
--   - reading: V_i(S)^{γ_i} (and (Σ_j v_ij z_ij)^{γ_i} in (7), (8)) at total weight 0 → 0 when the weight is 0, Real.rpow otherwise; reason: the paper uses V_i(∅)^{γ_i}(R_i(∅) − x̂) = 0 (p. 41) and an assortment of total weight 0 is never chosen (p. 7); Real.rpow gives 0^0 = 1 at γ_i = 0, which the model allows
--   - encoding: y_i ≥ max_{z_i ∈ [0,1]^n} of the objective of (7) → y_i ≥ the objective at every z ∈ [0,1]^n; reason: equivalent whenever the maximum exists (Lemma 6); needs no supremum
--   - encoding: v_i0 = 0 (§4); products {1,…,n}; N_ij = {1,…,j}, j ∈ N_+; S_i ⊂ N; optimal solution of (4); R_i(∅) = 0 → prefWeight without v_i0; Fin n, 0-based; nbr j; every Finset (Fin n); FeasibleNBR with least x (IsOptimalNBR); x/0 = 0; reason: Lean conventions; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), §4.2, p. 20, unnumbered

import Mathlib
import Definitions.Def_NestedLogitNBR_Feasible7
import Definitions.Def_NestedLogitNBR_FeasibleFull

namespace NestedLogitNBR

/-- **Problem (3) is a relaxation of problem (7).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), §4.2, p. 20, unnumbered: "The way it is formulated, problem (3) is a relaxed version of
problem (7) in the sense that any feasible solution `(x, y)` to problem (7) is also feasible to
problem (3)."

No hypothesis on the data is needed. -/
theorem feasible7_feasibleFull {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ)
    (x : ℝ) (y : Fin m → ℝ) (h : Feasible7 v0 r v γ x y) :
    FeasibleFull v0 r v γ x y := by sorry

end NestedLogitNBR
