-- Prove2me | Theorems.Thm_LinMaxLoad_Supplement_theorem_18
-- name    : LinMaxLoad.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:27:15.69921+00:00
-- url     : https://prove2.me/theorems/1c8c619a-873a-4063-b61f-b7def19a5ff0
-- title:
--   Theorem 18 — $\mathbb E_h[M(S,h)] \ge 2 - 1/n$ for $|S| = p^\ell$, with equality iff $S$ is an affine space
-- statement:
--   Let $p$ be a prime, let $h : \mathbb F_p^u \to \mathbb F_p^\ell$ be a uniformly random linear map, and let $S \subseteq \mathbb F_p^u$ be a set of size $n = p^\ell$. Then
--
--   $$
--   \mathbb E_h\bigl[M(S, h)\bigr] \ge 2 - \frac1n ,
--   $$
--
--   with equality if and only if $S$ is an affine space (necessarily of dimension $\ell$).
--
--   Thus affine subspaces are exactly the minimizers of the expected linear max load among sets of size $p^\ell$, matching the value $m(V) = 2 - p^{-\ell}$ computed for subspaces in Lemma 4.
--
--   Differences from the source:
--   - encoding: $\mathbb F_p^u$; $\mathbb E_h[M(S,h)]$; “$S$ is an affine space” → `Fin u → ZMod p`; published `expLoad` with $r = \ell$; $S$ equals the carrier of an `AffineSubspace`; reason: Lean convention; same instances
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Theorem 18, p.26 (introduction form Theorem 6, p.6)

import Mathlib
import Definitions.Def_LinMaxLoad_expLoad

namespace LinMaxLoad.Supplement

open LinMaxLoad

/-- **Theorem 18** (p.26; introduction form Theorem 6, p.6) of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `h : F_p^u → F_p^ℓ` be a random linear map, and let `S ⊆ F_p^u` be a set of size `n = p^ℓ`.
Then `E_h[M(S, h)] ≥ 2 − 1/n`, with equality iff `S` is an affine space.

**Formalization Note** `E_h[M(S, h)]` is the published `expLoad` with `r = ℓ` (uniform over all
linear maps). "`S` is an affine space" is: the set `S` equals the carrier of an affine subspace
of `F_p^u` (such a subspace has `p^ℓ` points, i.e. dimension `ℓ`, as in Theorem 6). -/
theorem theorem_18 (p : ℕ) [Fact p.Prime] (u ℓ : ℕ) (S : Finset (Fin u → ZMod p))
    (hS : S.card = p ^ ℓ) :
    2 - 1 / ((p ^ ℓ : ℕ) : ℝ) ≤ expLoad (ZMod p) (Fin u → ZMod p) ℓ S ∧
      (expLoad (ZMod p) (Fin u → ZMod p) ℓ S = 2 - 1 / ((p ^ ℓ : ℕ) : ℝ) ↔
        ∃ A : AffineSubspace (ZMod p) (Fin u → ZMod p),
          (S : Set (Fin u → ZMod p)) = (A : Set (Fin u → ZMod p))) := by sorry

end LinMaxLoad.Supplement
