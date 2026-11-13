-- Prove2me | Theorems.Thm_GlobalSinkhorn_cycle_identity
-- name    : GlobalSinkhorn.cycle_identity
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T04:23:08.233547+00:00
-- url     : https://prove2.me/theorems/bc7c2068-e01d-4408-873e-8f802f110776
-- title:
--   Proof of Theorem 3.1 — one column–row cycle sends $M(w)$ to $M(\mathcal F(w))$
-- statement:
--   Let $n\ge2$, let $S$ be a nonnegative doubly stochastic $n\times n$ matrix, and let $w\in\mathbb R^n_{>0}$. Then
--   1. $M(w)$ is row-stochastic;
--   2. for every $j$ the $j$-th column sum of $M(w)$ equals $w_j/\mathcal F(w)_j$, and this number is positive;
--   3. normalizing the columns of $M(w)$ and then the rows of the result gives $M(\mathcal F(w))$:
--   $$
--   \mathcal R\big(\mathcal C(M(w))\big)=M(\mathcal F(w)).
--   $$
--
--   Here $M(w)=\operatorname{diag}((Sw)^{-1})S\operatorname{diag}(w)$ and $\mathcal F(w)=[S^\top(Sw)^{-1}]^{-1}$. This identity writes the Sinkhorn–Knopp dynamics as the vector map $\mathcal F$.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: S nonnegative and doubly stochastic → S ∈ doublyStochastic ℝ (Fin n) (entries ≥ 0, all row and column sums 1); reason: Mathlib's doubly stochastic matrices are exactly the paper's
--   - encoding: M(w), F(w) defined with (Sw)⁻¹ and [Sᵀ(Sw)⁻¹]⁻¹ for w > 0 → Lean's total inverse in Mw, Fw; reason: for w > 0 and doubly stochastic S every inverted entry is positive (p.15), so the junk value 0 is never used
--   - encoding: column normalization, then row normalization → rowNormalize (colNormalize (Mw S w)) with Lean's total division; reason: the column sums w_j/F(w)_j and row sums (S F(w))_i/(Sw)_i are positive, so total division never fires
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), proof of Theorem 3.1, pp.18–19

import Mathlib
import Definitions.Def_GlobalSinkhorn_rowNormalize
import Definitions.Def_GlobalSinkhorn_colNormalize
import Definitions.Def_GlobalSinkhorn_Mw
import Definitions.Def_GlobalSinkhorn_Fw

open Matrix

namespace GlobalSinkhorn

/-- `M(w)` is row-stochastic with column sums `wⱼ / F(w)ⱼ > 0`, and one full column–row
normalization cycle sends `M(w)` to `M(F(w))`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), proof of Theorem 3.1, pp.18–19. -/
theorem cycle_identity {n : ℕ} (hn : 2 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    Mw S w ∈ Matrix.rowStochastic ℝ (Fin n) ∧
      (∀ j, ∑ i, Mw S w i j = w j / Fw S w j ∧ 0 < w j / Fw S w j) ∧
      rowNormalize (colNormalize (Mw S w)) = Mw S (Fw S w) := by sorry

end GlobalSinkhorn
