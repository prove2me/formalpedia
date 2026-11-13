-- Prove2me | Theorems.Thm_HDXHitting_affine_identity
-- name    : HDXHitting.affine_identity
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T17:57:53.781613+00:00
-- url     : https://prove2.me/theorems/6745ed2b-63b9-4073-b1d5-b6878eb7af53
-- title:
--   Proof of Lemma 3.2 (partite) — $\partial_ic_d=c_{d-1}(\vec\mu_{-i}+\lambda\mathbf 1)$ and $c_d(\vec\mu-h\vec e_i)+h\,\partial_ic_d(\vec\mu)=c_d(\vec\mu)$
-- statement:
--   Let $S$ be a set of $d=|S|\ge2$ colours, $i\in S$, $\lambda\in\mathbb R$, $\vec\mu$ a vector and $h\in\mathbb R$. With $c_d$ the polynomial of (3) over $S$ and $c_{d-1}$ the same polynomial over $S\setminus\{i\}$:
--   1. the partial derivative of $c_d$ in the $i$-th coordinate is
--   $$
--   \partial_i c_d(\vec\mu)=c_{d-1}(\vec\mu_{-i}+\lambda\mathbf 1);
--   $$
--   2. since $c_d$ is affine in the $i$-th coordinate,
--   $$
--   c_d(\vec\mu-h\vec e_i)+h\,c_{d-1}(\vec\mu_{-i}+\lambda\mathbf 1)=c_d(\vec\mu).
--   $$
--   This closes the induction in the proof of the partite bound (3).
--
--   Differences from the source:
--   - generalization: nonnegative vectors µ⃗ and h = h_v ≥ 0 → every real vector µ, every h ∈ ℝ, every λ ∈ ℝ; reason: polynomial identities; they specialize to the page's values
--   - encoding: c_d and c_{d−1} for the d-partite complex → cPoly over S with |S| = d ≥ 2 and over S ∖ {i}; reason: the page uses the identity in the inductive step d ≥ 2; at |S| = 1, c_0 is undefined (1/0)
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), proof of Lemma 3.2 (partite bound), p.17

import Mathlib
import Definitions.Def_HDXHitting_cPoly

namespace HDXHitting

/-- The partial derivative of `c_d` and the affine identity (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), proof of Lemma 3.2,
p.17: "differentiation gives `∂_i c_d(µ) = c_{d−1}(µ_{−i} + λ1)`. Since `c_d` is affine in the
`i`-th coordinate, … `c_d(µ − h_v e⃗_i) + h_v ∂_i c_d(µ⃗) = c_d(µ⃗)`"): for a colour set `S` with
`|S| = d ≥ 2`, `i ∈ S`, any `µ` and any `h`,
1. `∂_i c_d(µ) = c_{d−1}(µ_{−i} + λ1)`, with `c_{d−1}` over `S ∖ {i}`;
2. `c_d(µ − h e⃗_i) + h c_{d−1}(µ_{−i} + λ1) = c_d(µ)`. -/
theorem affine_identity {ι : Type*} [DecidableEq ι] (S : Finset ι) (hS : 2 ≤ S.card) (i : ι)
    (hi : i ∈ S) (lam : ℝ) (μ : ι → ℝ) (h : ℝ) :
    HasDerivAt (fun t => cPoly S lam (Function.update μ i t))
        (cPoly (S.erase i) lam (fun j => μ j + lam)) (μ i) ∧
      cPoly S lam (μ - h • Pi.single i 1) + h * cPoly (S.erase i) lam (fun j => μ j + lam) =
        cPoly S lam μ := by sorry

end HDXHitting
