-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_Supplement_theorem_1_3
-- name    : HypercliqueAC0.FixedDepth.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:27:54.808036+00:00
-- url     : https://prove2.me/theorems/c0354134-f1ff-4712-88f1-de0558433d2f
-- title:
--   Theorem 1.3: depth-$h$ circuits for $k$-OV in dimension $d\ge(\log n)^{O_{h,\varepsilon}(1)}$ need $n^{k(1-\varepsilon)}$ gates
-- statement:
--   An instance of $k\text{-}\mathsf{OV}_{n,d}$ consists of $k$ lists $A_i=(a_{i,1},\dots,a_{i,n})$ of vectors in $\{0,1\}^d$, and
--   $$k\text{-}\mathsf{OV}_{n,d}(A_1,\dots,A_k)=1\iff\exists(j_1,\dots,j_k)\in[n]^k:\ \bigwedge_{i=1}^k a_{i,j_i}=0^d .$$
--   A depth-$h$ circuit is a De Morgan circuit of depth at most $h$, $G(C)$ is its number of noninput gates, and $\log$ is the base-two logarithm. The theorem has two claims.
--
--   1. For every integer $h\ge1$ and every $\varepsilon>0$ there is an exponent $K$, depending only on $h$ and $\varepsilon$, such that for every fixed $k\ge2$ there is $n_0$ with the following property: for every $n\ge n_0$ and every dimension $d\ge(\log n)^K$, every depth-$h$ circuit $C$ computing $k\text{-}\mathsf{OV}_{n,d}$ satisfies
--   $$G(C)\ge n^{k(1-\varepsilon)}.$$
--   2. For every integer $h\ge1$, every $\varepsilon>0$ and every $k\ge2$ there are an exponent $K'$ and $n_0$ such that for every $n\ge n_0$ and every $d\ge(\log n)^{K'}$, every depth-$h$ circuit $C$ computing $k\text{-}\mathsf{OV}_{n,d}$ satisfies
--   $$G(C)\ge n^{k-\varepsilon}.$$
--
--   The exhaustive-search circuit uses about $n^k$ gates, so the bound shows that exhaustive search is nearly optimal for $k$-OV at every fixed depth in polylogarithmic dimension.
--
--   **Formalization Note** $k\text{-}\mathsf{OV}_{n,d}$ is the published `ErrAmpOV.kOV k n d`, whose variable `(i, j, q)` is coordinate $q$ of vector $j$ of list $i$. In the first claim the exponent $K$ is chosen before $k$, so it is uniform in $k$; in the second it may depend on $k$. Every dimension $d$ above the threshold is covered.
--
--   Differences from the source:
--   - encoding: $k$ lists of $n$ vectors in $\{0,1\}^d$ → Boolean variables indexed by $\mathrm{Fin}\,k\times\mathrm{Fin}\,n\times\mathrm{Fin}\,d$ (the published `ErrAmpOV.kOV`); reason: a relabeling bijection preserves every instance
--   - encoding: integers $h,k,n,d$ and the threshold for "sufficiently large $n$" → natural numbers, with real casts before exponentiation; reason: all are counts or lower thresholds, and a natural threshold can dominate any integer threshold
--   - encoding: the §3.2 convention that every gate reaches the output → arbitrary circuits, including unused gates and repeated input sources, with gate count equal to the gate-list length; reason: pruning unused gates and deleting repeated sources preserve output and depth and cannot increase gate count
--   - reading: "$d\ge(\log n)^{O_{h,\varepsilon}(1)}$" in the first claim → there is a real exponent $K$ chosen after $h,\varepsilon$ and before $k$, and the claim holds for every $d\ge(\log n)^K$; reason: the subscript names exactly $h,\varepsilon$, and the proof takes $K=\lceil r/\theta\rceil+1$ depending only on $h,\varepsilon$
--   - reading: "$d\ge(\log n)^{O_{h,k,\varepsilon}(1)}$" in the second claim → there is a real exponent $K'$ chosen after $h,\varepsilon,k$; reason: the subscript names exactly $h,k,\varepsilon$
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.4 (PDF p.6), Theorem 1.3; k-OV defined in §3.1 p.10 (PDF p.12); proof §7 pp.22-23 (PDF pp.24-25)

import Mathlib
import Definitions.Def_MantriCVQ_ACCircuit
import Definitions.Def_ErrAmpOV_kOV

noncomputable section

namespace HypercliqueAC0.FixedDepth.Supplement

/-- Theorem 1.3, p. 4 (PDF 6), both claims. `k-OV_{n,d}` is `ErrAmpOV.kOV k n d` on the
variables `Fin k × Fin n × Fin d`; `log` is base two. First claim: the exponent `K` of the
dimension threshold `(log n)^K` depends only on `h, ε` (it is chosen before `k`), and the
threshold `n₀` on `h, ε, k`. Second claim: the exponent `K'` may depend on `h, k, ε`. Every
dimension `d` above the threshold is covered. -/
theorem theorem_1_3 :
    (∀ h : ℕ, 1 ≤ h → ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ d : ℕ, (Real.logb 2 n) ^ K ≤ (d : ℝ) →
        ∀ C : MantriCVQ.ACCircuit (Fin k × Fin n × Fin d), C.depth ≤ h →
          (∀ x, C.eval x = ErrAmpOV.kOV k n d x) →
          (n : ℝ) ^ ((k : ℝ) * (1 - ε)) ≤ (C.gates.length : ℝ)) ∧
    (∀ h : ℕ, 1 ≤ h → ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 2 ≤ k → ∃ K : ℝ,
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ d : ℕ, (Real.logb 2 n) ^ K ≤ (d : ℝ) →
        ∀ C : MantriCVQ.ACCircuit (Fin k × Fin n × Fin d), C.depth ≤ h →
          (∀ x, C.eval x = ErrAmpOV.kOV k n d x) →
          (n : ℝ) ^ ((k : ℝ) - ε) ≤ (C.gates.length : ℝ)) := by sorry

end HypercliqueAC0.FixedDepth.Supplement
