-- Prove2me | Theorems.Thm_IterRoundDet_lemma_3_1
-- name    : IterRoundDet.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:53:28.370411+00:00
-- url     : https://prove2.me/theorems/abb80142-4578-4d5e-965c-1b64aa51786c
-- title:
--   Lemma 3.1 — the support is a matroid, $\log p$ is concave, and the Rayleigh property
-- statement:
--   Let $p=\sum_S c_S z^S$ be a multi-affine homogeneous degree-$d$ stable polynomial. Then:
--
--   1. the sets $\{S:c_S>0\}$ are the bases of a matroid $\mathcal N$ on $[n]$;
--   2. $\log p$ is a concave function of $z$, on the non-negative points where $p>0$;
--   3. (Rayleigh property) for every $x\in\mathbb R^n$ and all $i,j$,
--
--   $$\partial_j p(x)\,\partial_i p(x)\ge\partial_i\partial_j p(x)\,p(x).$$
--
--   The paper states these without proof, from Borcea, Brändén and Liggett. Items 2 and 3 carry the concavity of the relaxation and the negative correlation behind $C_{ij}\le 0$.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
--   - reading: log p(z) is a concave function of z, no domain named → ConcaveOn on {z ≥ 0 : p(z) > 0}; reason: this is where Real.log p is a genuine logarithm and contains every point Lemma 3.3 uses, including x with zero coordinates
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.1, p.12

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.1, p.12 (stated there without proof, from [BBL09]). Let `p = ∑_S c_S z^S` be a
multi-affine homogeneous degree-`d` stable polynomial. Then (1) `{S : c_S > 0}` are the bases of a matroid;
(2) `log p` is concave; (3) (Rayleigh) for `x ∈ ℝⁿ`, `∂_j p(x) ∂_i p(x) ≥ ∂_i∂_j p(x) p(x)`.

**Formalization Note.** In (2) the domain is the closed positive orthant intersected with `{p > 0}`, where
`log p` is a genuine real logarithm: it contains the open orthant and the boundary points that Lemma 3.3
uses. (3) holds at every real point and for all `i, j`; at `i = j` the second derivative is `0`. -/
theorem lemma_3_1 {n d : ℕ} {c : Finset (Fin n) → ℝ} (hc : IsStablePoly d c) :
    (∃ N : Matroid (Fin n), N.E = Set.univ ∧ ∀ S : Finset (Fin n), N.IsBase (S : Set (Fin n)) ↔ 0 < c S) ∧
    ConcaveOn ℝ {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ 0 < pEval c z} (fun z => Real.log (pEval c z)) ∧
    ∀ (x : Fin n → ℝ) (i j : Fin n),
      partialAt (partialAt (pEval c) j) i x * pEval c x ≤
        partialAt (pEval c) j x * partialAt (pEval c) i x := by sorry

end IterRoundDet
