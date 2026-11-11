-- Prove2me | Theorems.Thm_OptTwoSrcExt_lemma_3_7
-- name    : OptTwoSrcExt.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:05.562909+00:00
-- url     : https://prove2.me/theorems/1b70ca76-9d2f-46e2-b269-eb03eea3219d
-- title:
--   Lemma 3.7 — forcing every field value: $\sigma_D(z)=\alpha^D$ when $D$ of $2D-1$ coordinates equal $\alpha$
-- statement:
--   Let $D$ be a power of two, $s=2D-1$, and $F$ a field of characteristic two, and let $\sigma_D$ be the elementary symmetric polynomial of degree $D$ in $s$ variables.
--
--   1. If any specified $D$ of $z_1,\dots,z_s\in F$ equal $\alpha$, then, for arbitrary values of the other coordinates,
--   $$\sigma_D(z_1,\dots,z_s)=\alpha^D .\tag{3.15}$$
--   2. On Boolean inputs $z\in\{0,1\}^s\subseteq F$, $\sigma_D$ is strict majority: $\sigma_D(z)=1$ if more than half of the coordinates equal $1$, and $\sigma_D(z)=0$ otherwise.
--
--   The merger of the sumset seed applies $\sigma_D$ to $2D-1$ field-valued views; this lemma lets a majority of good views force any prescribed output value.
--
--   **Formalization Note** $\sigma_D(z)$ is `Multiset.esymm` of $\{z_1,\dots,z_s\}$ at degree $D$; "characteristic two" is `CharP F 2`; strict majority is $2\cdot\#\{i:z_i=1\}>s$.
--
--   Differences from the source:
--   - encoding: σ_D(z_1, …, z_s); strict majority → Multiset.esymm of the multiset of coordinates at degree D; 2·#{i : z_i = 1} > s; reason: Lean convention; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Lemma 3.7, p.33 (PDF p.35)

import Mathlib

namespace OptTwoSrcExt

/-- **Lemma 3.7 (Forcing every field value).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Lemma 3.7, printed p.33 (PDF p.35): "Let D be a power of
two, let s = 2D − 1, and let F have characteristic two. If any specified D of z1, . . . , zs equal α,
then σD(z1, . . . , zs) = α^D (3.15) for arbitrary values of the other coordinates. On Boolean inputs,
σD is strict majority."

Let `D = 2^j`, `s = 2D − 1`, and `F` a field of characteristic two; `σ_D` is the elementary symmetric
polynomial of degree `D` in `s` variables.
1. If `z ∈ F^s` has `z_i = α` for all `i` in some set `S` of `D` indices, then `σ_D(z) = α^D`.
2. If every `z_i ∈ {0, 1}`, then `σ_D(z) = 1` when more than half of the `s` coordinates equal `1`,
   and `σ_D(z) = 0` otherwise.

**Formalization Note.** `σ_D(z)` is `Multiset.esymm` of the multiset `{z₁, …, z_s}` at degree `D`;
"strict majority" is `2·#{i : z_i = 1} > s`. -/
theorem lemma_3_7 {F : Type*} [Field F] [CharP F 2] [DecidableEq F] (D : ℕ) (hD : ∃ j : ℕ, D = 2 ^ j) :
    (∀ (z : Fin (2 * D - 1) → F) (α : F) (S : Finset (Fin (2 * D - 1))),
        S.card = D → (∀ i ∈ S, z i = α) →
          (Finset.univ.val.map z).esymm D = α ^ D) ∧
    (∀ z : Fin (2 * D - 1) → F, (∀ i, z i = 0 ∨ z i = 1) →
        (Finset.univ.val.map z).esymm D =
          if 2 * D - 1 < 2 * (Finset.univ.filter fun i => z i = 1).card then 1 else 0) := by sorry

end OptTwoSrcExt
