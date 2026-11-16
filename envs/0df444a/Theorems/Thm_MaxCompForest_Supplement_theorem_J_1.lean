-- Prove2me | Theorems.Thm_MaxCompForest_Supplement_theorem_J_1
-- name    : MaxCompForest.Supplement.theorem_J_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:29:53.907203+00:00
-- url     : https://prove2.me/theorems/e8cbe01a-cd5b-4879-aa91-4ee1fad995d7
-- title:
--   Theorem J.1 — connected minor-free quantization with $C_h=O((1+\log h)^2)$, (J.1)–(J.3)
-- statement:
--   Let $G$ be a connected positive-conductance graph excluding $K_h$ as a minor, $h\ge3$, with actual degrees $D$, $1\le q<n$, and $\lambda_{q+1}(D^{-1/2}LD^{-1/2})\ge\gamma>0$. There are constants $C_h$, depending only on $h$, with $C_h\le C(1+\log h)^2$ for an absolute $C$, such that:
--
--   1. for every finite-dimensional feature map $\Phi$ there are at most $\min(n,2q)$ original-row centers whose $D$-weighted error is at most
--   $$\frac{C_h}{\gamma}E_G(\Phi),\tag{J.1}$$
--   and a partition into at most that many nonempty connected blocks whose weighted mean error is at most (J.1);
--   2. one signal-independent law on such connected partitions satisfies
--   $$\mathbb E\,S_Q\preceq\frac{C_h}{\gamma}L,\qquad S_Q=D(I-P_Q);\tag{J.2}$$
--   3. for each integer $s\ge0$, at most $\min(n,q+s)$ original-row centers, and connected blocks, suffice with error at most
--   $$\frac{C_h}{9}\Big(1+\frac{8q}{s+1}\Big)\frac{E_G(\Phi)}{\gamma},\tag{J.3}$$
--   and some signal-independent law on these connected partitions has the same coefficient in its expected Loewner bound.
--
--   For fixed $h$ all constants are independent of the feature dimension, $n$, $q$, $s$, conductance ratios and the feature aspect ratio. This gives the connected-block clause of Theorem 5.3.
--
--   **Formalization Note** The laws are quantified before the feature map (signal independence); "such connected partitions" have at most $\min(n,2q)$, respectively $\min(n,q+s)$, blocks. Minor exclusion is for the underlying simple graph.
--
--   Differences from the source:
--   - encoding: C_h = O((1 + log h)²), the same C_h in (J.1)–(J.3) → ∃ C > 0 and a function Ch : ℕ → ℝ with Ch h ≤ C(1 + log h)² for h ≥ 3, fixed before every graph, q, s, γ, dimension and map; reason: C_h depends on h only; the O is absolute
--   - encoding: "one signal-independent law on such connected partitions" → a probability mass function on connected partitions with at most min(n, 2q) blocks, quantified before Φ; reason: signal independence is independence of the law from the signal
--   - encoding: a connected positive-conductance graph → a connected loopless WGraph, parallel labelled edges allowed; reason: parallel conductances can equivalently be aggregated (p.7), so a multigraph is the same instance as its aggregated graph; minors and connected blocks use the underlying simple graph
--   - encoding: at most m original-row centers with D-weighted error ≤ X → ∃ nonempty row set C, |C| ≤ m, with degree-weighted assignment cost ≤ X; reason: the paper's OPTrow convention
--   - encoding: graphs on arbitrary finite vertex and edge sets → vertex and edge types in Type with Fintype and DecidableEq; reason: every finite graph is isomorphic to one on such types
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem J.1, p.59 (PDF p.61)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_rowCost
import Definitions.Def_MaxCompForest_rowDist
import Definitions.Def_MaxCompForest_energy
import Definitions.Def_MaxCompForest_Supplement_expResid
import Definitions.Def_MaxCompForest_Supplement_blockMeanErr
import Definitions.Def_MaxCompForest_Supplement_IsConnPartition
import Definitions.Def_MaxCompForest_Supplement_ExcludesCliqueMinor
open EffResSparsify.ResistanceSketch
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **Theorem J.1 (Connected minor-free quantization).** Let `G` be a connected positive-conductance graph excluding `K_h`
as a minor, `h ≥ 3`, `D` its actual degrees, `1 ≤ q < n`, `λ_{q+1}(D^{−1/2}LD^{−1/2}) ≥ γ > 0`. With
`C_h = O((1+log h)²)`:

* for every finite-dimensional `Φ`, at most `min(n, 2q)` original-row centers have `D`-weighted error at most
  `(C_h/γ) E_G(Φ)` (J.1), and some partition into at most that many nonempty connected blocks has weighted mean error
  at most (J.1);
* one signal-independent law on such connected partitions satisfies `E S_Q ⪯ (C_h/γ) L` (J.2);
* for each `s ≥ 0`, at most `min(n, q+s)` row centers and connected blocks suffice with error at most
  `(C_h/9)(1 + 8q/(s+1)) E_G(Φ)/γ` (J.3), and some signal-independent law on these connected partitions has the same
  coefficient in its expected Loewner bound.

Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem J.1, p.59.

**Formalization Note.** `C_h` is one function of `h` alone with `C_h ≤ C(1+log h)²` for an absolute `C`, fixed before
every graph, `q`, `s`, `γ`, dimension and map; the same `C_h` is used in (J.1)–(J.3). The laws are quantified before the
feature map (signal independence). "Such connected partitions" are connected partitions with at most `min(n, 2q)`
(respectively `min(n, q+s)`) blocks. `E S_Q ⪯ X` is `(X − E S_Q).PosSemidef`. -/
theorem theorem_J_1 :
    ∃ (C : ℝ) (Ch : ℕ → ℝ), 0 < C ∧ (∀ h : ℕ, 3 ≤ h → Ch h ≤ C * (1 + Real.log h) ^ 2) ∧
      ∀ (h : ℕ), 3 ≤ h →
      ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : WGraph V E), G.IsConnected → ExcludesCliqueMinor G.toSimpleGraph h →
        ∀ (q : ℕ), 1 ≤ q → q < Fintype.card V →
        ∀ (γ : ℝ), 0 < γ → γ ≤ MaxCompForest.lam G (MaxCompForest.deg G) q →
          (∀ {d : ℕ} (x : V → EuclideanSpace ℝ (Fin d)),
            (∃ (Cs : Finset V) (hC : Cs.Nonempty), Cs.card ≤ min (Fintype.card V) (2 * q) ∧
              MaxCompForest.rowCost (MaxCompForest.deg G) (MaxCompForest.rowDist x) Cs hC ≤
                Ch h / γ * MaxCompForest.energy G x) ∧
            (∃ Q : Finpartition (Finset.univ : Finset V), Q.parts.card ≤ min (Fintype.card V) (2 * q) ∧
              IsConnPartition G Q ∧
              blockMeanErr (MaxCompForest.deg G) x Q ≤ Ch h / γ * MaxCompForest.energy G x)) ∧
          (∃ μ : PMF (Finpartition (Finset.univ : Finset V)),
            (∀ Q ∈ μ.support, Q.parts.card ≤ min (Fintype.card V) (2 * q) ∧ IsConnPartition G Q) ∧
            ((Ch h / γ) • G.laplacian - expResid (MaxCompForest.deg G) μ).PosSemidef) ∧
          ∀ s : ℕ,
            (∀ {d : ℕ} (x : V → EuclideanSpace ℝ (Fin d)),
              (∃ (Cs : Finset V) (hC : Cs.Nonempty), Cs.card ≤ min (Fintype.card V) (q + s) ∧
                MaxCompForest.rowCost (MaxCompForest.deg G) (MaxCompForest.rowDist x) Cs hC ≤
                  Ch h / 9 * (1 + 8 * q / ((s : ℝ) + 1)) * MaxCompForest.energy G x / γ) ∧
              (∃ Q : Finpartition (Finset.univ : Finset V), Q.parts.card ≤ min (Fintype.card V) (q + s) ∧
                IsConnPartition G Q ∧
                blockMeanErr (MaxCompForest.deg G) x Q ≤
                  Ch h / 9 * (1 + 8 * q / ((s : ℝ) + 1)) * MaxCompForest.energy G x / γ)) ∧
            ∃ μ : PMF (Finpartition (Finset.univ : Finset V)),
              (∀ Q ∈ μ.support, Q.parts.card ≤ min (Fintype.card V) (q + s) ∧ IsConnPartition G Q) ∧
              ((Ch h / 9 * (1 + 8 * q / ((s : ℝ) + 1)) / γ) • G.laplacian -
                expResid (MaxCompForest.deg G) μ).PosSemidef := by sorry

end MaxCompForest.Supplement
