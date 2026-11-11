-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_retained_quadratic_minima
-- name    : MaxCutMatrix2027.Upper.retained_quadratic_minima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T12:48:15.728417+00:00
-- url     : https://prove2.me/theorems/4aa83a26-904f-451e-ac23-5fac795b913e
-- title:
--   Lemma 4.5 — Retained quadratic minima
-- statement:
--   Let $G$ be any simple graph on $n$ vertices, let $1\le s\le n$ be real, and let $0<\tau\le1$. Let $L$ be the part of its adjacency matrix retaining precisely the eigenvalues with $|\theta_j|>\tau n$. For independent Bernoulli$(s/n)$ selectors, write $P$ for their diagonal matrix. Then
--   $$\mathbb E\left|\min_{x\in[-1,1]^n}\frac{x^TPLPx}{s^2}-\min_{x\in[-1,1]^n}\frac{x^TLx}{n^2}\right|\le\frac8{\sqrt s}+\frac{17}{\tau s}.$$
--   Both minima are over the full continuous cube. The diagonal of $L$ may be nonzero; replacing these minima by minima over cut signs would change the statement. Zero retained rank is included. This is the retained-spectrum contribution to the MAX-CUT sampling error.
--
--   Differences from the source:
--   - encoding: vertices labelled by [n] and independent Bernoulli selectors → Fin n and the exact finite Bernoulli-subset expectation; reason: relabeling is bijective and the subset weights are exactly the independent-selector law
--   - encoding: continuous-cube minima of the two normalized objectives → real infima of continuous quadratic images of the compact nonempty cube, divided by the positive normalization; reason: these extrema are attained and positive scaling commutes with the minimum
--   - encoding: any orthonormal eigenbasis for L → Mathlib's chosen orthonormal eigenbasis; reason: the retained spectral operator is independent of the basis chosen in an eigenspace
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma 4.5, Eq.(15), p.20 (PDF p.20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
set_option autoImplicit false

namespace MaxCutMatrix2027.Upper

/-- Lemma 4.5, p.20, Eq.(15). Minima range over the continuous cube. -/
theorem retained_quadratic_minima (n : ℕ) (G : SimpleGraph (Fin n)) (s τ : ℝ)
    (hs : 1 ≤ s) (hsn : s ≤ n) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    sampleAverage (s / n) (fun Q =>
      |cubeMin (restrictMatrix Q (retainedMatrix G τ)) / s ^ 2 -
       cubeMin (retainedMatrix G τ) / (n : ℝ) ^ 2|) ≤
      8 / Real.sqrt s + 17 / (τ * s) := by sorry

end MaxCutMatrix2027.Upper
