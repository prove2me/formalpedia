-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_hidden_matching_as_regression
-- name    : FourWayStream.ARHM.Supplement.hidden_matching_as_regression
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:01:32.35718+00:00
-- url     : https://prove2.me/theorems/27c5a270-67ed-4036-b0c0-2ba362b5b98f
-- title:
--   Lemma 5.18 — Hidden Matching as regression: $B_k$ orthogonal and $p_{B_k,y}(e,b)=\frac2N\mathbf 1[b=x_u\oplus x_v]$
-- statement:
--   Let $N$ be even, $F=\{F_1,\dots,F_{N-1}\}$ a one-factorization of $K_N$, each pair oriented arbitrarily, and $B_k=U_{F_k}^\top$, where $(U_My)_{(e,0)}=(y_u+y_v)/\sqrt2$ and $(U_My)_{(e,1)}=(y_u-y_v)/\sqrt2$. Then:
--   1. $B_k$ is orthogonal, $B_kB_k^\top=I$ and $B_k^\top B_k=I$, so all its singular values equal $1$ and its condition number is $1$: $\|B_k\beta\|=\|\beta\|$ for every $\beta$.
--   2. Every row and every column of $B_k$ has exactly two nonzero entries, each $\pm1/\sqrt2$.
--   3. For a promised $y$, $y_j=(-1)^{x_j}/\sqrt N$: $B_k^+y=U_{F_k}y$, it has norm $1$, and
--   $$p_{B_k,y}(e,b)=\frac2N\cdot\mathbf 1[b=x_u\oplus x_v]\qquad(e=\{u,v\}\in F_k,\ b\in\{0,1\}).$$
--
--   So the ideal regression sampler outputs a uniform pair of $F_k$ together with its parity: on this family regression sampling is Hidden Matching.
--
--   **Formalization Note** "Condition number $1$" is stated as the isometry property. $B_k^+$ is the Moore–Penrose pseudoinverse defined by the four Penrose conditions.
--
--   Differences from the source:
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
--   - encoding: condition number 1 → ‖B_k β‖₂ = ‖β‖₂ for every β (every singular value is 1); reason: for an orthogonal matrix this is the same statement
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.26, Lemma 5.18 (proof p.43, Appendix A)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Supplement_Regression

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Lemma 5.18 (Hidden Matching as regression), p.26 (proof p.43). Let `N` be even, `F` a
one-factorization of `K_N`, `ori` an orientation of the pairs and `B_k = U_{F_k}ᵀ`. Then `B_k` is
orthogonal (`B_k B_kᵀ = I`, `B_kᵀ B_k = I`), so every singular value is `1` (condition number `1`:
`‖B_k β‖ = ‖β‖`); every row and every column of `B_k` has exactly two nonzero entries, each
`±1/√2`. For a promised `y = (−1)^x/√N`, `B_k⁺ y = U_{F_k} y`, it has norm `1`, and
`p_{B_k,y}(e, b) = (2/N) · 1[b = x_u ⊕ x_v]` for `e = {u, v} ∈ F_k`, `b ∈ {0, 1}`. -/
theorem hidden_matching_as_regression (N : ℕ) (hN : Even N)
    (F : Fin (N - 1) → Finset (Sym2 (Fin N))) (hF : IsOneFactorization F)
    (ori : Sym2 (Fin N) → Fin N × Fin N) (hori : IsOrientation ori) (k : Fin (N - 1)) :
    (hmB F ori k * (hmB F ori k)ᵀ = 1 ∧ (hmB F ori k)ᵀ * hmB F ori k = 1) ∧
    (∀ β : rowSet (F k) → ℝ, ∑ j, ((hmB F ori k).mulVec β j) ^ 2 = ∑ p, β p ^ 2) ∧
    (∀ j : Fin N, (Finset.univ.filter (fun p => hmB F ori k j p ≠ 0)).card = 2) ∧
    (∀ p : rowSet (F k), (Finset.univ.filter (fun j => hmB F ori k j p ≠ 0)).card = 2) ∧
    (∀ j p, hmB F ori k j p ≠ 0 → |hmB F ori k j p| = 1 / Real.sqrt 2) ∧
    ∀ x : Fin N → Bool,
      (pinv (hmB F ori k)).mulVec (flatVec x) = (hmU (F k) ori).mulVec (flatVec x) ∧
      ∑ p, ((pinv (hmB F ori k)).mulVec (flatVec x) p) ^ 2 = 1 ∧
      ∀ p : rowSet (F k), lsProb (hmB F ori k) (flatVec x) p =
        2 / (N : ℝ) * (if p.1.2 = edgeParity x p.1.1 then 1 else 0) := by sorry

end FourWayStream.ARHM.Supplement
