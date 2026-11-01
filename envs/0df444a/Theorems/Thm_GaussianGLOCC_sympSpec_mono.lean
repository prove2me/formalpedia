-- Prove2me | Theorems.Thm_GaussianGLOCC_sympSpec_mono
-- name    : GaussianGLOCC.sympSpec_mono
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:51.558531+00:00
-- url     : https://prove2.me/theorems/5a81d7bb-1a40-42ab-90c9-cf88cf5716b4
-- title:
--   Lemma 2: the ordered symplectic spectrum is monotone in the Loewner order
-- statement:
--   Let $M_1$, $M_2$ be real symmetric positive semidefinite $2n\times 2n$ matrices and let $s(M_1)$, $s(M_2)$ be their vectors of symplectic eigenvalues in ascending order. Then
--
--   $$
--   M_1\ge M_2\quad\Longrightarrow\quad s(M_1)_k\ge s(M_2)_k\qquad\text{for all }k=1,\dots,n.
--   $$
--
--   This is the tool that turns the matrix inequality (25) into the comparison $r\ge r'$ of squeezing vectors.
--
--   Differences from the source:
--   - reading: real positive 2n × 2n matrices M1, M2 ≥ 0 → M₁, M₂ real symmetric positive semidefinite (Mathlib PosSemidef); reason: the printed condition is ≥ 0; the proof's strict positivity is the narrower reading and is not a hypothesis of the statement
--   - encoding: M1 ≥ M2; indices k = 1, …, n → (M₁ − M₂).PosSemidef; k : Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, Lemma 2, eq. (11), p.4 (proof p.5)

import Mathlib
import Definitions.Def_GaussianGLOCC_sympSpec
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, Lemma 2 (Symplectic spectrum), p.4:
"Consider real positive 2n × 2n matrices M1, M2 ≥ 0. Let s(M1) and s(M2) be the vectors
consisting of the (ascendingly ordered) symplectic eigenvalues of M1 and M2, respectively. Then
M1 ≥ M2 =⇒ s(M1)k ≥ s(M2)k ∀ k = 1, . . . , n. (11)"

For real symmetric positive semidefinite `2n × 2n` matrices `M₁`, `M₂` with `M₁ − M₂`
positive semidefinite, the `k`-th smallest symplectic eigenvalue of `M₁` is at least that of
`M₂`, for every `k`.

**Formalization Note.** "real positive … ≥ 0" is read as positive semidefinite (Mathlib
`PosSemidef` includes symmetry), the printed "≥ 0"; the proof on p.5 assumes strict
positivity, which is not a hypothesis of the statement. `sympSpec` is 0-indexed. -/
theorem sympSpec_mono {n : ℕ} (M₁ M₂ : Cov n) (h₁ : M₁.PosSemidef) (h₂ : M₂.PosSemidef)
    (h : (M₁ - M₂).PosSemidef) : ∀ k, sympSpec M₂ k ≤ sympSpec M₁ k := by sorry

end GaussianGLOCC
