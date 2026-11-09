-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_minor_expansion_and_vanishing
-- name    : OddPermSum.Evaluation.minor_expansion_and_vanishing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:17:28.044146+00:00
-- url     : https://prove2.me/theorems/ec0ae357-0155-4651-8e3b-c528357d6919
-- title:
--   Lemma 3.1 — complementary minors and rank vanishing
-- statement:
--   For every square matrix $A$ over a commutative ring of characteristic two,
--
--   $$\Phi(A)=\sum_{i<j,\ k>l}A_{i,k}A_{j,l}\det A[-\{i,j\},-\{k,l\}].$$
--
--   In addition, for every square matrix over a characteristic-two field,
--
--   $$\operatorname{rank}A+3\le n\ \Longrightarrow\ \Phi(A)=0.$$
--
--   The ring identity and the field consequence are retained together. Complementary minors inherit the original orders, including determinant one at order zero. This is the scalar rank-vanishing result; it does not assert that the gradient vanishes at corank three.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → increasing zero-based Fin n indices; reason: the order-preserving bijection changes no matrix, summation inequality or instance
--   - encoding: rank A ≤ n − 3 → Matrix.rank A + 3 ≤ n; reason: avoids truncated natural subtraction and expresses exactly the source integer inequality
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 6, Lemma 3.1, Eqs. (3.1)–(3.2)

import Definitions.Def_OddPermSum_Evaluation_phi
import Definitions.Def_OddPermSum_Evaluation_orderedMinor

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Lemma 3.1, both (3.1) and (3.2). The second bound avoids truncated subtraction. -/
theorem minor_expansion_and_vanishing :
    (∀ (R : Type*) [CommRing R] [CharP R 2] (n : ℕ)
      (A : Matrix (Fin n) (Fin n) R),
      phi A = ∑ i, ∑ j, ∑ k, ∑ l,
        if i < j ∧ l < k then A i k * A j l * complementaryMinor A i j k l else 0) ∧
    (∀ (F : Type*) [Field F] [CharP F 2] (n : ℕ)
      (A : Matrix (Fin n) (Fin n) F), Matrix.rank A + 3 ≤ n → phi A = 0) := by sorry

end OddPermSum.Evaluation
