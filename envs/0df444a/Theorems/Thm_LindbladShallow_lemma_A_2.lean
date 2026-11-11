-- Prove2me | Theorems.Thm_LindbladShallow_lemma_A_2
-- name    : LindbladShallow.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:17:25.656086+00:00
-- url     : https://prove2.me/theorems/a8013986-cb2b-4b19-b775-89502a622cdd
-- title:
--   Lemma A.2 — Hamiltonian Cayley approximation
-- statement:
--   For $H=H^\dagger$, $h\ge0$ and $h\|H\|\le1$, let $C_H(h)=(I-ihH/2)(I+ihH/2)^{-1}$. Then
--   $$\|C_H(h)-e^{-ihH}\|\le\frac{h^3\|H\|^3}{12},\qquad \|\mathrm{Ad}_{C_H(h)}-e^{h\mathcal H_H}\|_\diamond\le\frac{h^3\|H\|^3}{6},$$
--   where $\mathcal H_H(Z)=-i[H,Z]$ and $\mathrm{Ad}_U(Z)=UZU^\dagger$.
--
--   This is the per-step error of the Hamiltonian collision gate, used in Lemma A.4.
--
--   Differences from the source:
--   - encoding: ‖Φ‖_⋄ = sup_{r≥1} sup_{Z≠0} ‖(Φ⊗I_r)(Z)‖₁/‖Z‖₁ → dnorm: an ℝ≥0∞ supremum over every r ≥ 1 and every nonzero complex Z, reference factor first (id_r ⊗ Φ), trace norm QAlgorithms.traceNorm; reason: Lean convention; reordering tensor factors changes no value and the ℝ≥0∞ supremum has no junk value
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma A.2, p.59, Eq. (61)

import Mathlib
import Definitions.Def_LindbladShallow_gksl

open scoped Matrix ComplexOrder ENNReal

namespace LindbladShallow

/-- **Lemma A.2** (Hamiltonian Cayley approximation; arXiv:2610.05362, held version
sha256 8f4637ef…, p.59). For `H = H†`, `h ≥ 0` and `h‖H‖ ≤ 1`, let
`C_H(h) := (I − ihH/2)(I + ihH/2)^{−1}`. Then
`‖C_H(h) − e^{−ihH}‖ ≤ h³‖H‖³/12` and `‖Ad_{C_H(h)} − e^{hℋ_H}‖_⋄ ≤ h³‖H‖³/6` (61),
with `ℋ_H(Z) = −i[H, Z]` and `Ad_U(Z) = UZU†`. -/
theorem lemma_A_2 {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hH : H.IsHermitian) (h : ℝ) (hh : 0 ≤ h) (hhH : h * opNorm H ≤ 1) :
    opNorm (cayley ((h : ℂ) • H) - NormedSpace.exp ((-(Complex.I * (h : ℂ))) • H)) ≤
        h ^ 3 * opNorm H ^ 3 / 12 ∧
      dnorm (QAlgorithms.conjSuperop (cayley ((h : ℂ) • H)) - ⇑(supExp h (hamSup H))) ≤
        ENNReal.ofReal (h ^ 3 * opNorm H ^ 3 / 6) := by sorry

end LindbladShallow
