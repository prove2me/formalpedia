-- Prove2me | Theorems.Thm_HybridXorLift_lemma_3_1
-- name    : HybridXorLift.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:13:59.125617+00:00
-- url     : https://prove2.me/theorems/8cd8b23a-f2af-445e-984c-74183d688f48
-- title:
--   Lemma 3.1 — one-bit kernel: eigenvectors of $L$, $ZLZ \preceq e^{2\tau}L$, $L^{-1/2}ZL^{-1/2} = Z$, $-L \preceq Z \preceq L$
-- statement:
--   Let $q \ge 1$, $\tau = 1/(2q)$, and let $L$ and $Z$ be the one-bit kernel and the sign matrix. Then:
--
--   1. the all-ones vector and the vector $(1,-1)$ are eigenvectors of $L$, with eigenvalues $e^{-\tau}$ and $e^{\tau}$;
--   2. $Z L Z \preceq e^{2\tau} L$;
--   3. $L^{-1/2} Z L^{-1/2} = Z$;
--   4. $-L \preceq Z \preceq L$.
--
--   Here $A \preceq B$ means that $B - A$ is positive semidefinite. The first inequality says that flipping the sign of one bit costs at most a factor $e^{2\tau} = e^{1/q}$ in the quadratic form; the identity in item 3 is used for the conditioning step.
--
--   **Formalization Note** $L^{-1/2}$ is the inverse of the positive square root of $L$; item 3 is stated for every positive semidefinite $S$ with $S^2 = L$, which is that (unique) square root. The vector $(1,-1)$ has entry $1$ at the bit $0$.
--
--   Differences from the source:
--   - encoding: L^{-1/2}, the inverse of the positive square root of L → S⁻¹ for every positive semidefinite S with S * S = L; reason: the positive semidefinite square root exists and is unique
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Lemma 3.1, p.12 (PDF p.14)

import Definitions.Def_HybridXorLift_kernelL
import Definitions.Def_HybridXorLift_signZ

namespace HybridXorLift

/-- Lemma 3.1 (One-bit kernel) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.12 (PDF p.14). For `τ = 1/(2q)`, the all-ones vector
and `(1, −1)` are eigenvectors of `L` with eigenvalues `e^{−τ}` and `e^{τ}`, and
`ZLZ ⪯ e^{2τ} L`, `L^{−1/2} Z L^{−1/2} = Z`, `−L ⪯ Z ⪯ L` (3.4).

**Formalization Note** `A ⪯ B` is `(B − A).PosSemidef`. `L^{−1/2}` is the inverse of the positive
square root of `L`; the clause is stated for every positive semidefinite `S` with `S * S = L`,
which is that square root (it is unique). The vector `(1, −1)` has entry `1` at the bit `0`
(`false`). -/
theorem lemma_3_1 (q : ℕ) (hq : 1 ≤ q) :
    (kernelL q).mulVec (fun _ => 1) = Real.exp (-(1 / (2 * (q : ℝ)))) • (fun _ => 1) ∧
    (kernelL q).mulVec (fun b => if b then -1 else 1) =
      Real.exp (1 / (2 * (q : ℝ))) • (fun b => if b then -1 else 1) ∧
    (Real.exp (2 * (1 / (2 * (q : ℝ)))) • kernelL q - signZ * kernelL q * signZ).PosSemidef ∧
    (∀ S : Matrix Bool Bool ℝ, S.PosSemidef → S * S = kernelL q → S⁻¹ * signZ * S⁻¹ = signZ) ∧
    (signZ + kernelL q).PosSemidef ∧ (kernelL q - signZ).PosSemidef := by sorry

end HybridXorLift
