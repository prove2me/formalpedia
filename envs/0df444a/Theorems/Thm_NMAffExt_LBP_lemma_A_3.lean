-- Prove2me | Theorems.Thm_NMAffExt_LBP_lemma_A_3
-- name    : NMAffExt.LBP.lemma_A_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:29:06.3778+00:00
-- url     : https://prove2.me/theorems/cdc24229-62d1-457d-be5b-5994944b9391
-- title:
--   Lemma A.3 — intersecting projected sections: $|\mathbb E_a h(B(a))h(B'(a))-c|\le 2\varepsilon(1-c)$
-- statement:
--   Let $F:\mathbb F_2^n\to\mathbb F_2^m$ be $(k,\varepsilon)$ non-malleable against globally fixed-point-free affine involutions (in particular, any $(k,\varepsilon)$ non-malleable affine extractor), let $u\in\mathbb F_2^m$ be nonzero, and put $h(x)=(-1)^{\langle u,F(x)\rangle}$. Suppose affine maps $B,B':\mathbb F_2^d\to\mathbb F_2^n$ satisfy $Q_0B=Q_0B'=J$, i.e. $Q_0B(a)=Q_0B'(a)=Ja$ for all $a$, where $Q_0\in\mathbb F_2^{r\times n}$ and $J\in\mathbb F_2^{r\times d}$ are linear maps of rank $q\ge k+1$. With $c=\Pr_{a\sim U_d}[B(a)=B'(a)]$,
--   $$\Bigl|\mathbb E_{a\sim U_d}\,h(B(a))\,h(B'(a))-c\Bigr|\le 2\varepsilon(1-c).\qquad\text{(A.4)}$$
--
--   The lemma replaces section decorrelation when the projected sections of Lemma A.1 may intersect; it is the extractor input to Theorem A.4.
--
--   Differences from the source:
--   - generalization: the codomain of $Q_0$ and $J$ is not stated (Lemma A.1 uses $\mathbb F_2^q$) → any $\mathbb F_2^r$, with both maps of rank $q$; reason: the case $r=q$ is the source's statement in Lemma A.1's setting.
--   - reading: "Let F be a $(k,\varepsilon)$ non-malleable affine extractor … Non-malleability against globally fixed-point-free affine involutions suffices" → hypothesis `IsNMAffExtInv k ε F`; reason: the lemma's last sentence; implied by `IsNMAffExt k ε F`, so both sentences are covered.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 102 (PDF 104), Lemma A.3, eq. (A.4)

import Mathlib
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_NMAffExt_LBP_Basic
import Definitions.Def_NMAffExt_LBP_NonMalleable

open Matrix

namespace NMAffExt.LBP

/-- **Lemma A.3.** Let `F` be `(k, ε)` non-malleable against globally fixed-point-free affine
involutions, `u ≠ 0`, `h(x) = (−1)^{⟨u, F(x)⟩}`. If affine `B, B' : 𝔽₂ᵈ → 𝔽₂ⁿ` satisfy
`Q₀B = Q₀B' = J` for linear maps `Q₀`, `J` of rank `q ≥ k + 1`, and
`c = Pr_{a∼U_d}[B(a) = B'(a)]`, then `|E_a h(B(a)) h(B'(a)) − c| ≤ 2ε(1 − c)`. -/
theorem lemma_A_3 (n m k d q r : ℕ) (ε : ℝ) (F : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (hF : IsNMAffExtInv k ε F) (u : Fin m → ZMod 2) (hu : u ≠ 0)
    (B B' : (Fin d → ZMod 2) → (Fin n → ZMod 2))
    (hB : QuadExt.Main.IsAffineMap B) (hB' : QuadExt.Main.IsAffineMap B')
    (Q₀ : Matrix (Fin r) (Fin n) (ZMod 2)) (J : Matrix (Fin r) (Fin d) (ZMod 2))
    (hQ₀ : Q₀.rank = q) (hJ : J.rank = q) (hq : k + 1 ≤ q)
    (hQB : ∀ a, Q₀ *ᵥ B a = J *ᵥ a) (hQB' : ∀ a, Q₀ *ᵥ B' a = J *ᵥ a) :
    |avg (fun a : Fin d → ZMod 2 => sgn (ip u (F (B a))) * sgn (ip u (F (B' a)))) -
        avg (fun a : Fin d → ZMod 2 => if B a = B' a then (1 : ℝ) else 0)| ≤
      2 * ε * (1 - avg (fun a : Fin d → ZMod 2 => if B a = B' a then (1 : ℝ) else 0)) := by sorry

end NMAffExt.LBP
