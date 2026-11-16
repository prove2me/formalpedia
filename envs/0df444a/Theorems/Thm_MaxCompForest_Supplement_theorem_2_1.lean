-- Prove2me | Theorems.Thm_MaxCompForest_Supplement_theorem_2_1
-- name    : MaxCompForest.Supplement.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:23:10.645715+00:00
-- url     : https://prove2.me/theorems/7b1a4762-b8ed-4a3f-91de-3a2d7e988f1f
-- title:
--   Theorem 2.1 — sharp graph quantization: (2.1), (2.2), the $2q$ budget, $\Omega(\min\{d,\log(q+1)\})$ sharpness and a $144$-approximate rational algorithm
-- statement:
--   Let $H$ be a connected loopless multigraph with positive conductances, weighted degrees $d_v$, $D=\mathrm{diag}(d_v)$ and normalized Laplacian $N_H=D^{-1/2}L_HD^{-1/2}$ with eigenvalues $\lambda_1\le\dots\le\lambda_n$. Let $1\le q<n$ and $\lambda_{q+1}(N_H)\ge\gamma>0$. For a map $\Phi:V(H)\to\mathbb R^d$ write $E_H(\Phi)=\sum_{uv\in E(H)}c_{uv}\|\Phi_u-\Phi_v\|^2$ and $\mathrm{OPT}^{\mathrm{row}}_b(\Phi)$ for the least degree-weighted squared error of replacing $\Phi$ by at most $b$ of its own rows (budgets capped at $n$). There are absolute constants $C,C_2,c>0$ such that:
--
--   1. For every $d\ge1$, every $\Phi$ and every integer $s\ge0$,
--   $$\mathrm{OPT}^{\mathrm{row}}_{q+s}(\Phi)\le\Big(\frac{432q}{s+1}+2952d\Big)\frac{E_H(\Phi)}{\gamma},\tag{2.1}$$
--   $$\mathrm{OPT}^{\mathrm{row}}_{q+s}(\Phi)\le C\Big(\frac{q}{s+1}+\log(q+s+1)\Big)\frac{E_H(\Phi)}{\gamma}.\tag{2.2}$$
--   2. In particular $2q$ rows suffice with coefficient $C_2\min\{d,\log(q+1)\}$.
--   3. For every $q,d\ge1$ there is a connected graph with positive rational conductances, $n>2q$ vertices and $\lambda_{q+1}\ge1/100$, and a map $\Phi$ with $E(\Phi)>0$, such that even with arbitrary real centers
--   $$\frac{(1/100)\,\mathrm{OPT}^{\mathrm{real}}_{2q}(\Phi)}{E(\Phi)}\ \ge\ c\,\min\{d,\log(q+1)\}.$$
--   4. A deterministic algorithm whose running time is $(L+2)^b$ for an absolute exponent $b$, on rational graph and feature inputs of total binary length $L$, returns at most $\min(n,q+s)$ distinct rows whose cost is at most $144$ times each of the right-hand sides of (2.1) and (2.2).
--
--   The theorem shows that a few original rows quantize any graph-smooth feature map, with a dimension-free logarithmic coefficient, and that this coefficient is necessary at budget $2q$.
--
--   **Formalization Note** All constants, the machine and its exponent are fixed before every graph, map and parameter. In the algorithmic clause $\gamma$ is not an input: the output meets both bounds for every admissible $\gamma$. $\log$ is the natural logarithm. Machines are Mathlib's multi-stack Turing machines (`TM2ComputableAux`) with the base mission's binary encoders.
--
--   Differences from the source:
--   - encoding: OPTrow_b(Φ) ≤ X → ∃ a nonempty row set C with |C| ≤ min(n, b) and weighted assignment cost ≤ X; reason: the minimum over finitely many row sets is attained; budgets are capped at n (p.7)
--   - encoding: O(·) and Ω(·) coefficients and the constant C of (2.2) → constants C, C₂, c > 0 existentially quantified before every graph, map, q, s, d; reason: the constants are absolute
--   - encoding: graphs on arbitrary finite vertex and edge sets → vertex and edge types in Type with Fintype and DecidableEq; reason: every finite graph is isomorphic to one on such types
--   - reading: "a connected rational weighted graph with n > 2q and λ_{q+1} ≥ 1/100 attains Ω(min{d, log(q+1)}) at that same budget, even allowing arbitrary real centers" → an explicit rational input graph, connected, with more than 2q vertices and λ_{q+1} ≥ 1/100, and a real map Φ with E(Φ) > 0 and c·min{d, log(q+1)} ≤ (1/100)·OPTreal_{2q}(Φ)/E(Φ); reason: the attained coefficient is γ·OPT/E with γ = 1/100, as Theorem B.1 makes explicit; OPTreal ≤ OPTrow, so the row-center lower bound follows
--   - reading: "a deterministic absolute-exponent polynomial-time algorithm attains 144 times either row-center upper bound with the same budget" → one TM2 machine and absolute exponent b; on every connected rational input with λ_{q+1} > 0 it outputs at most min(n, q+s) distinct rows meeting 144 × (2.1) and 144 × (2.2) for every admissible γ, within (L+2)^b steps; reason: one output meeting both bounds is the stronger reading; the algorithm reads q and s, and γ is only a hypothesis of the bounds
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 2.1, p.6 (PDF p.8); standing assumptions §2.1, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_RInst
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_rowCost
import Definitions.Def_MaxCompForest_rowDist
import Definitions.Def_MaxCompForest_energy
import Definitions.Def_MaxCompForest_ratFeat
import Definitions.Def_MaxCompForest_encIndices
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_MaxCompForest_Supplement_optReal
import Definitions.Def_MaxCompForest_Supplement_encQuantIn
open EffResSparsify.ResistanceSketch
open OnlineCRS.Combine (Sym)
open CFLOutliers (OutputsWithin)
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **Theorem 2.1 (Sharp graph quantization).** With degree masses on a connected loopless positively weighted
multigraph `H` with `λ_{q+1}(N_H) ≥ γ > 0`, `1 ≤ q < n`:

* (2.1) `OPTrow_{q+s}(Φ) ≤ (432q/(s+1) + 2952d) E_H(Φ)/γ` for every `s ≥ 0` and every `Φ : V → ℝ^d`, `d ≥ 1`;
* (2.2) `OPTrow_{q+s}(Φ) ≤ C (q/(s+1) + log(q+s+1)) E_H(Φ)/γ`;
* `2q` rows suffice with coefficient `O(min{d, log(q+1)})`;
* sharpness: for every `q, d ≥ 1` some connected rational weighted graph with `n > 2q` and `λ_{q+1} ≥ 1/100` and some
  `Φ` have `γ·OPTreal_{2q}(Φ)/E(Φ) ≥ c·min{d, log(q+1)}` with `γ = 1/100` (real centers, hence also rows);
* a deterministic algorithm with an absolute exponent, on rational graph and feature inputs, returns at most
  `min(n, q+s)` rows within `144` times either upper bound.

Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 2.1, p.6; standing assumptions §2.1, p.7.

**Formalization Note.** `OPTrow_b ≤ X` is `∃` a nonempty row set of size at most `min(n, b)` (budgets are capped at
`n`, p.7) with cost at most `X`. All constants (`C`, `C₂`, `c`, the machine `M` and the exponent `b`) are chosen
before every graph, map and parameter. The upper bounds are stated for graphs on vertex and edge types in `Type`.
In the algorithmic clause `γ` is not an input: the output meets both bounds for every admissible `γ`, i.e. with
`γ = λ_{q+1}`. `log` is the natural logarithm. -/
theorem theorem_2_1 :
    ∃ (C C₂ c : ℝ) (M : Turing.TM2ComputableAux Sym Sym) (b : ℕ), 0 < C ∧ 0 < C₂ ∧ 0 < c ∧
      (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (H : WGraph V E), H.IsConnected →
        ∀ (q : ℕ), 1 ≤ q → q < Fintype.card V →
        ∀ (γ : ℝ), 0 < γ → γ ≤ MaxCompForest.lam H (MaxCompForest.deg H) q →
        ∀ {d : ℕ}, 1 ≤ d → ∀ (x : V → EuclideanSpace ℝ (Fin d)),
          (∀ s : ℕ, ∃ (Cs : Finset V) (hC : Cs.Nonempty), Cs.card ≤ min (Fintype.card V) (q + s) ∧
            MaxCompForest.rowCost (MaxCompForest.deg H) (MaxCompForest.rowDist x) Cs hC ≤
              (432 * q / ((s : ℝ) + 1) + 2952 * d) * MaxCompForest.energy H x / γ) ∧
          (∀ s : ℕ, ∃ (Cs : Finset V) (hC : Cs.Nonempty), Cs.card ≤ min (Fintype.card V) (q + s) ∧
            MaxCompForest.rowCost (MaxCompForest.deg H) (MaxCompForest.rowDist x) Cs hC ≤
              C * ((q : ℝ) / ((s : ℝ) + 1) + Real.log ((q : ℝ) + s + 1)) * MaxCompForest.energy H x / γ) ∧
          (∃ (Cs : Finset V) (hC : Cs.Nonempty), Cs.card ≤ min (Fintype.card V) (2 * q) ∧
            MaxCompForest.rowCost (MaxCompForest.deg H) (MaxCompForest.rowDist x) Cs hC ≤
              C₂ * min (d : ℝ) (Real.log ((q : ℝ) + 1)) * MaxCompForest.energy H x / γ)) ∧
      (∀ q d : ℕ, 1 ≤ q → 1 ≤ d →
        ∃ I : MaxCompForest.RInst, I.graph.IsConnected ∧ 2 * q < I.n ∧
          (1 / 100 : ℝ) ≤ MaxCompForest.lam I.graph (MaxCompForest.deg I.graph) q ∧
          ∃ x : Fin I.n → EuclideanSpace ℝ (Fin d), 0 < MaxCompForest.energy I.graph x ∧
            c * min (d : ℝ) (Real.log ((q : ℝ) + 1)) ≤
              (1 / 100 : ℝ) * optReal (MaxCompForest.deg I.graph) x (2 * q) / MaxCompForest.energy I.graph x) ∧
      (∀ (I : MaxCompForest.RInst) (q s d : ℕ) (x : Fin d → Fin I.n → ℚ),
        I.graph.IsConnected → 1 ≤ q → q < I.n → 1 ≤ d →
        0 < MaxCompForest.lam I.graph (MaxCompForest.deg I.graph) q →
        ∃ (Cs : List (Fin I.n)) (hC : Cs.toFinset.Nonempty), Cs.Nodup ∧ Cs.length ≤ min I.n (q + s) ∧
          (∀ γ : ℝ, 0 < γ → γ ≤ MaxCompForest.lam I.graph (MaxCompForest.deg I.graph) q →
            MaxCompForest.rowCost (MaxCompForest.deg I.graph) (MaxCompForest.rowDist (MaxCompForest.ratFeat x))
                Cs.toFinset hC ≤
              144 * ((432 * q / ((s : ℝ) + 1) + 2952 * d) *
                MaxCompForest.energy I.graph (MaxCompForest.ratFeat x) / γ) ∧
            MaxCompForest.rowCost (MaxCompForest.deg I.graph) (MaxCompForest.rowDist (MaxCompForest.ratFeat x))
                Cs.toFinset hC ≤
              144 * (C * ((q : ℝ) / ((s : ℝ) + 1) + Real.log ((q : ℝ) + s + 1)) *
                MaxCompForest.energy I.graph (MaxCompForest.ratFeat x) / γ)) ∧
          OutputsWithin M (encQuantIn I q s x) (MaxCompForest.encIndices Cs)
            (((encQuantIn I q s x).length + 2) ^ b)) := by sorry

end MaxCompForest.Supplement
