-- Prove2me | Theorems.Thm_OracleSNARG_PublicLB_pairwise_bound
-- name    : OracleSNARG.PublicLB.pairwise_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:48:39.918729+00:00
-- url     : https://prove2.me/theorems/c7f55301-f21b-4372-ad79-c224323a00e6
-- title:
--   §6, pairwise-independence bound — $\Pr_h[E_{\mathrm{crs},r}]\ge p-|B|p^2\ge 1/(4\ell)$ with $p=2^{-k}=1/(2\ell)$
-- statement:
--   Let $h:\{0,1\}^n\to\{0,1\}^k$ be drawn from a pairwise-independent family $H$, where $2^k=2\ell$ (so $\ell\ge1$ is a power of two), and let $p=2^{-k}=1/(2\ell)$. Let $x\in\{0,1\}^n$ and let $B\subseteq\{0,1\}^n$ be a finite set with $x\notin B$ and $|B|\le\ell$. Then
--   $$\Pr_h\big[h(x)=0^k\ \wedge\ \forall u\in B,\ h(u)\ne0^k\big]\ \ge\ p-|B|\,p^2\qquad\text{and}\qquad \Pr_h\big[h(x)=0^k\ \wedge\ \forall u\in B,\ h(u)\ne0^k\big]\ \ge\ \frac1{4\ell}.$$
--   In the proof of Theorem 22, $x=x_{\mathrm{crs}}$ and $B=B_{\mathrm{crs},r}$, the other rows visited by the verifier under $O_1$, which do not depend on $h$. The bound says the row $x_{\mathrm{crs}}$ is marked while no other visited row is, with probability at least $1/(4\ell)$.
--
--   Differences from the source:
--
--   - generalization: x_crs and B_{crs,r} (a set fixed independently of h, with x_crs ∉ B_{crs,r} and |B_{crs,r}| ≤ ℓ) → any point x and any finite set B with x ∉ B and |B| ≤ ℓ; reason: the display uses only these properties, so it specializes to B = B_{crs,r}
--   - encoding: k = log2(2ℓ) with ℓ a power of 2 (footnote 9) → the hypothesis 2^k = 2ℓ; reason: the same condition
--   - encoding: probabilities → the real value of the PMF's outer measure of the event; reason: Lean convention
-- source:
--   Goldwasser, Kalai, Incrementally Verifiable Oracle Aided Computation, STOC 2027 submission (manuscript sha256 cc66f0af…), p. 26, §6, display after 'By pairwise independence and a union bound' (footnotes 9-10)

import Mathlib
import Definitions.Def_OracleSNARG_PublicLB_ProofObjects

set_option autoImplicit false

namespace OracleSNARG.PublicLB

/-- **§6, pairwise-independence bound**, p. 26 of Goldwasser, Kalai (manuscript sha256
cc66f0af…): "By pairwise independence and a union bound, Pr_h[E_{crs,r}] ≥ Pr_h[h(x_crs) = 0^k] −
Σ_{u∈B_{crs,r}} Pr_h[h(x_crs) = 0^k ∧ h(u) = 0^k] = p − |B_{crs,r}|·p^2 ≥ p − ℓp^2 = … = 1/(4ℓ)",
with `p = 2^{-k} = 1/(2ℓ)`. Stated for every pairwise-independent family `h : {0,1}^n → {0,1}^k`
with `2^k = 2ℓ`, every point `x` and every finite set `B` of points with `x ∉ B` and
`|B| ≤ ℓ`. -/
theorem pairwise_bound (n k ℓ : ℕ) (hk : 2 ^ k = 2 * ℓ) (H : PMF (Hash n k))
    (hH : IsPairwiseIndep H) (x : Fin n → Bool) (B : Finset (Fin n → Bool)) (hxB : x ∉ B)
    (hB : B.card ≤ ℓ) :
    ((2 : ℝ) ^ k)⁻¹ - (B.card : ℝ) * ((2 : ℝ) ^ k)⁻¹ ^ 2 ≤
        (H.toOuterMeasure {h | h x = (fun _ => false) ∧
          ∀ u ∈ B, h u ≠ (fun _ => false)}).toReal ∧
      1 / (4 * (ℓ : ℝ)) ≤
        (H.toOuterMeasure {h | h x = (fun _ => false) ∧
          ∀ u ∈ B, h u ≠ (fun _ => false)}).toReal := by sorry

end OracleSNARG.PublicLB
