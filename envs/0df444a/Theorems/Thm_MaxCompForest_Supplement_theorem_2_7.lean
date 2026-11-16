-- Prove2me | Theorems.Thm_MaxCompForest_Supplement_theorem_2_7
-- name    : MaxCompForest.Supplement.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:23:53.762689+00:00
-- url     : https://prove2.me/theorems/8717b24f-c008-4d40-9c64-11c2864fe4f7
-- title:
--   Theorem 2.7 — logarithmic and near-$q$ row budgets (2.12), (2.13)
-- statement:
--   Let $L$ be the Laplacian of a finite loopless weighted graph on $n\ge2$ vertices (possibly disconnected), $W=\mathrm{diag}(w_v)$ positive vertex masses, $N_W=W^{-1/2}LW^{-1/2}$, $1\le q<n$ and $\lambda_{q+1}(N_W)\ge\gamma>0$. Let $C_{CW}\ge1$ be the universal integer chosen so that $C_{CW}\lceil\log_2(m+1)\rceil$ meets the dimension condition of the Charikar–Waingarten theorem. For every map $\Phi$ into a finite-dimensional Euclidean space, with budgets capped at $n$:
--
--   1. for each integer $s\ge0$,
--   $$\mathrm{OPT}^{\mathrm{row}}_{q+s}(\Phi)\le\frac{320}{81}\Big[\frac{432q}{s+1}+2952\,C_{CW}\lceil\log_2(q+s+1)\rceil\Big]\frac{E(\Phi)}{\gamma};\tag{2.12}$$
--   2. $2q$ rows have error $O(\log(q+1)E/\gamma)$, with an absolute constant;
--   3. for every $0<\varepsilon\le1$, at exactly the budget $\min(n,\lfloor(1+\varepsilon)q\rfloor)$,
--   $$\mathrm{OPT}^{\mathrm{row}}_{\lfloor(1+\varepsilon)q\rfloor}(\Phi)\le\frac{320}{81}\Big[\frac{432}{\varepsilon}+2952\,C_{CW}\lceil\log_2(2q+1)\rceil\Big]\frac{E(\Phi)}{\gamma}.\tag{2.13}$$
--
--   Here $\mathrm{OPT}^{\mathrm{row}}_b$ is the least $W$-weighted squared error of replacing $\Phi$ by at most $b$ of its own rows and $E(\Phi)=\sum_{uv}c_{uv}\|\Phi_u-\Phi_v\|^2$. The coefficient is thus $O(\log(q+1)+1/\varepsilon)$, independent of the feature dimension; this is the bound behind the partition laws of Section 5.
--
--   **Formalization Note** $\lceil\log_2 m\rceil$ is `Nat.clog 2 m`. The dimension is arbitrary, including $0$.
--
--   Differences from the source:
--   - reading: C_CW, "a universal integer ≥ 1 sufficiently large" for the cited dimension condition → ∃ CCW ≥ 1, quantified once before every graph, mass, q, s, ε, dimension and map; reason: the paper does not give its value, which depends on an unspecified constant of [CW25, Theorem 4]
--   - encoding: O(log(q+1)E/γ) → ∃ absolute C > 0 with the bound C·log(q+1)·E/γ; reason: the constant is absolute
--   - encoding: OPTrow_b(Φ) ≤ X → ∃ a nonempty row set C with |C| ≤ min(n, b) and weighted assignment cost ≤ X; reason: the minimum over finitely many row sets is attained; budgets are capped at n (p.7)
--   - encoding: graphs on arbitrary finite vertex and edge sets → vertex and edge types in Type with Fintype and DecidableEq; reason: every finite graph is isomorphic to one on such types
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 2.7, p.11 (PDF p.13); C_CW p.11; hypotheses of Theorem 2.4 p.10 (PDF p.12) and §2.1 p.7 (PDF p.9)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_rowCost
import Definitions.Def_MaxCompForest_rowDist
import Definitions.Def_MaxCompForest_energy
open EffResSparsify.ResistanceSketch
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **Theorem 2.7 (Logarithmic and near-q row budgets).** Under the hypotheses of Theorem 2.4 (arbitrary positive
masses `W`, `λ_{q+1}(N_W) ≥ γ > 0`, `1 ≤ q < n`, the graph possibly disconnected), every map `Φ` into a finite-
dimensional Euclidean space satisfies, with budgets capped at `n`:

* (2.12) `OPTrow_{q+s}(Φ) ≤ (320/81)[432q/(s+1) + 2952 C_CW ⌈log₂(q+s+1)⌉] E(Φ)/γ` for every `s ≥ 0`;
* `2q` rows have error `O(log(q+1) E/γ)`;
* (2.13) `OPTrow_{⌊(1+ε)q⌋}(Φ) ≤ (320/81)[432/ε + 2952 C_CW ⌈log₂(2q+1)⌉] E(Φ)/γ` for every `0 < ε ≤ 1`, at
  exactly the budget `min(n, ⌊(1+ε)q⌋)`.

Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 2.7, p.11; `C_CW` p.11; hypotheses of Theorem 2.4, p.10 and §2.1, p.7.

**Formalization Note.** `C_CW` is "a universal integer `≥ 1` sufficiently large" whose value depends on an unspecified
constant of the cited theorem [CW25, Theorem 4]; it is existentially quantified once, before every graph, mass,
`q`, `s`, `ε`, dimension and map. `⌈log₂ m⌉` is `Nat.clog 2 m`. `OPTrow_b ≤ X` is `∃` a nonempty row set of size at
most `min(n, b)` with cost at most `X`. The dimension `d` is arbitrary (`d = 0` included). -/
theorem theorem_2_7 :
    ∃ (CCW : ℕ) (C : ℝ), 1 ≤ CCW ∧ 0 < C ∧
      ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : WGraph V E) (W : V → ℝ), (∀ v, 0 < W v) →
        ∀ (q : ℕ), 1 ≤ q → q < Fintype.card V →
        ∀ (γ : ℝ), 0 < γ → γ ≤ MaxCompForest.lam G W q →
        ∀ {d : ℕ} (x : V → EuclideanSpace ℝ (Fin d)),
          (∀ s : ℕ, ∃ (Cs : Finset V) (hC : Cs.Nonempty), Cs.card ≤ min (Fintype.card V) (q + s) ∧
            MaxCompForest.rowCost W (MaxCompForest.rowDist x) Cs hC ≤
              320 / 81 * (432 * q / ((s : ℝ) + 1) + 2952 * CCW * (Nat.clog 2 (q + s + 1) : ℝ)) *
                MaxCompForest.energy G x / γ) ∧
          (∃ (Cs : Finset V) (hC : Cs.Nonempty), Cs.card ≤ min (Fintype.card V) (2 * q) ∧
            MaxCompForest.rowCost W (MaxCompForest.rowDist x) Cs hC ≤
              C * Real.log ((q : ℝ) + 1) * MaxCompForest.energy G x / γ) ∧
          (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            ∃ (Cs : Finset V) (hC : Cs.Nonempty), Cs.card ≤ min (Fintype.card V) ⌊(1 + ε) * q⌋₊ ∧
              MaxCompForest.rowCost W (MaxCompForest.rowDist x) Cs hC ≤
                320 / 81 * (432 / ε + 2952 * CCW * (Nat.clog 2 (2 * q + 1) : ℝ)) *
                  MaxCompForest.energy G x / γ) := by sorry

end MaxCompForest.Supplement
