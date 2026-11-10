-- Prove2me | Theorems.Thm_OptRobustCD_lemma_5_8
-- name    : OptRobustCD.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:53:07.927311+00:00
-- url     : https://prove2.me/theorems/8254fc4c-e2d8-4fc7-9ef5-c2f7f2ec4df7
-- title:
--   Lemma 5.8 — preprocessing for robustness: in linear time, symmetric $\tilde M$ with $\|\tilde M-M_s(G)\|_{1,2}\le\varepsilon\sqrt n$, $\|\tilde M\|_{1,\infty}\le C$, linear-time products
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$, and $M_s$ as in Definition 5.5 with $L$ large enough. For every $s\in\mathbb N$ and $\varepsilon>0$ there are a linear-time algorithm, $C\ge1$ and $\eta>0$ which, with high probability over $G$, given as input any $n$-vertex graph $F$ with $|E(F)\triangle E(G)|\le\eta n$, produce a symmetric matrix $\tilde M\in\mathbb R^{n\times n}$ with
--   $$\|\tilde M-M_s(G)\|_{1,2}\le\varepsilon\sqrt n,\qquad \|\tilde M\|_{1,\infty}\le C.$$
--   Moreover, matrix-vector products by $\tilde M$ can be computed in linear time.
--
--   It feeds the robust recovery algorithm of Lemma 5.9 in the proof of Theorem 5.1.
--
--   Differences from the source:
--   - reading: L = L(d,λ) ⩾ 2 a sufficiently large constant (Definition 5.5) → ∃ L₀ ⩾ 2, ∀ L ⩾ L₀; reason: the meaning of 'sufficiently large'
--   - reading: a linear-time algorithm produces M̃; products by M̃ in linear time → two real-RAM programs (no oracle): P_pre halts within C′(n + |E(F)| + 1) steps on every input and tape and outputs a list D; on the event there is a symmetric M̃ with the two bounds such that P_mv on D ++ x halts within C′(n + |E(F)| + 1) steps and outputs M̃x, for every x; reason: the paper names no machine; 'produces M̃' means the output determines M̃ through its products
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 5.8, p.27 (pdf p.29); restated p.34 (pdf p.36)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_BetheHessian
import Definitions.Def_OptRobustCD_RowNorms
import Definitions.Def_OptRobustCD_Layouts

namespace OptRobustCD

/-- **Lemma 5.8** (Preprocessing for robustness). Hopkins, Hua, Mohanty, Rajaraman, Steurer,
*Optimal Robust Community Detection*, STOC 2027 submission (manuscript of November 3, 2026, sha256
3d287d54…), Lemma 5.8, p.27 (pdf p.29; restated p.34, pdf p.36).

"Let (G, σ⋆) ∼ SBM(n, d, λ) and dλ² > 1. For every s ∈ N and ε > 0, there is a linear-time algorithm,
C ⩾ 1 and η > 0 which with high probability over G, given as input any n-vertex graph F such that
|E(F)△E(G)| ⩽ ηn, produces a symmetric matrix `M̃ ∈ R^{n×n}` such that `∥M̃ − M_s(G)∥_{1,2} ⩽ ε√n`,
`∥M̃∥_{1,∞} ⩽ C`. Moreover, matrix-vector products by `M̃` can be computed in linear time."

**Formalization Note.**
* `M_s` depends on the constant `L` of Definition 5.5, "sufficiently large": the statement holds for
  every `L ⩾ L₀` for some `L₀ ⩾ 2`.
* The algorithm is a pair of real-RAM programs without oracle: `P_pre` reads a code of `F` and halts
  within `C′(n + |E(F)| + 1)` steps on every input and tape (linear time), producing a list `D`; on
  the event, there is a symmetric `M̃` with the two bounds such that `P_mv`, on input `D` followed by
  any `x ∈ R^n`, halts within `C′(n + |E(F)| + 1)` steps and outputs `M̃x`. The paper's `M̃` is
  `M_s(F_k)` (§7); the statement asserts only that the produced matrix has the properties.
* `d > 0`, `λ ∈ (−1, 1)` are the standing assumptions of §3.1. -/
theorem lemma_5_8 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) :
    ∃ L₀ : ℕ, 2 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ s : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ Ppre Pmv : Program, NoOracle Ppre ∧ NoOracle Pmv ∧ ∃ C : ℝ, 1 ≤ C ∧ ∃ C' : ℝ,
      ∃ η : ℝ, 0 < η ∧
      (∀ (n : ℕ) (F : SimpleGraph (Fin n)) (c : List ℝ), GraphCode F c →
        HaltsWithin Ppre noOracle c (C' * ((n : ℝ) + numEdges F + 1))) ∧
      Whp d lam (fun n _σ G => ∀ F : SimpleGraph (Fin n), (editDist F G : ℝ) ≤ η * n →
        ∀ c : List ℝ, GraphCode F c → ∃ Mt : Matrix (Fin n) (Fin n) ℝ, Mt.transpose = Mt ∧
          norm12 (Mt - Ms d lam L s G) ≤ ε * Real.sqrt n ∧ norm1inf Mt ≤ C ∧
          ∀ ω, ∀ x : Fin n → ℝ,
            HaltsWithin Pmv noOracle (finalOut Ppre noOracle c ω ++ List.ofFn x)
                (C' * ((n : ℝ) + numEdges F + 1)) ∧
            ∀ ω', finalOut Pmv noOracle (finalOut Ppre noOracle c ω ++ List.ofFn x) ω' =
              List.ofFn (Mt.mulVec x)) := by sorry

end OptRobustCD
