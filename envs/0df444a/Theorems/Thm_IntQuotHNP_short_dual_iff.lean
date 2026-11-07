-- Prove2me | Theorems.Thm_IntQuotHNP_short_dual_iff
-- name    : IntQuotHNP.short_dual_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:11.950487+00:00
-- url     : https://prove2.me/theorems/6b63cc58-fe92-48ff-9326-0733ff9f7e3b
-- title:
--   §3.3 — $Z_{\mathrm{target}}>u$ iff some $w\in\Lambda^*$ has $\|w\|_2<1/(pu)$ and $\langle v_{\mathrm{tar}},w\rangle\neq0$
-- statement:
--   Let $b$ be linearly independent, let $v\ne0$ be a lattice vector, and let $p>0$, $u\ge1$. Then
--   $$
--   Z_{\mathrm{target}}>u\iff\exists\,w\in\Lambda^*:\ \|w\|_2<\frac1{pu},\ \ \langle v,w\rangle\neq0 .
--   $$
--   This reduces the tail of $Z_{\mathrm{target}}$ to the existence of a short dual vector, which is the event counted in Lemma 4.4.
--
--   Differences from the source:
--   - generalization: an input passed to the common algorithm, with v = v_tar = Φ(px_1) and p a prime → any linearly independent family, any nonzero lattice vector v, real p > 0; reason: these are the properties of such an input that the equivalence uses
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §3.3, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_IntQuotHNP_DualLattice

open InnerProductSpace

namespace IntQuotHNP

/-- **§3.3: `Z_target > u` iff there is a short dual vector pairing nontrivially with `v_tar`.**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), §3.3, p.21 (PDF p.22): "For an input passed to the common algorithm and u ≥ 1, the
definition gives Z_target > u ⟺ ∃ w ∈ Λ∗ : ∥w∥₂ < 1/(pu), ⟨v_tar, w⟩ ≠ 0."

For linearly independent `b`, a nonzero lattice vector `v`, `p > 0` and `u ≥ 1`:
`Z_target > u` if and only if some `w ∈ Λ∗` has `‖w‖ < 1/(pu)` and `⟨v, w⟩ ≠ 0`.

**Formalization Note.** "An input passed to the common algorithm" supplies a lattice basis and the
nonzero lattice vector `v_tar = Φ(p x₁)`; these are the hypotheses here. -/
theorem short_dual_iff {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → EuclideanSpace ℝ κ)
    (v : EuclideanSpace ℝ κ) (p u : ℝ) (hb : LinearIndependent ℝ b) (hv : v ∈ latticeOf b)
    (hv0 : v ≠ 0) (hp : 0 < p) (hu : 1 ≤ u) :
    u < zTarget b v p ↔ ∃ w ∈ dualLattice b, ‖w‖ < 1 / (p * u) ∧ ⟪v, w⟫_ℝ ≠ 0 := by sorry

end IntQuotHNP
