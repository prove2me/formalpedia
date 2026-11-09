-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_strength_bounds
-- name    : LindbladTolerant.Testing.strength_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:57:57.048743+00:00
-- url     : https://prove2.me/theorems/5c7f12d1-8dd2-4fa0-bd1f-7d4215333b92
-- title:
--   Lemma 2.8 — Strength bounds
-- statement:
--   Let $n\ge1$, $d=2^n$, and let $\mathcal L$ be a time-independent $n$-qubit Lindblad generator. All jump representations below use finite traceless jump families and a Hermitian Hamiltonian. Write $C$ for the jump block, $A=\sum_aL_a^\dagger L_a$, $\mathcal D$ for the canonical dissipator, and $\Gamma=\operatorname{Tr}C$. When $\Gamma>0$, put $\sigma=C/\Gamma$, $\sigma_R=\operatorname{Tr}_S\sigma$, and $h(\sigma)=\operatorname{Tr}(\sigma^2)+(d\operatorname{Tr}(\sigma_R^2)-1)/2$.
--
--   The total canonical jump rate and canonical dissipative strength satisfy both bounds
--   $$\Gamma\le\|\mathcal L\|_\diamond,\qquad \|\mathcal D\|_F\le\frac{\|\mathcal L\|_\diamond}{\sqrt2}.$$
--   No locality or separate bound on the Hamiltonian is assumed. These inequalities control short-time approximation and determine the nontrivial threshold range.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Lemma 2.8, p.15, PDF p.15, Eq.(39)

import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem strength_bounds {n : ℕ} (hn : 1 ≤ n)
    (g : Super (Qubits n) (Qubits n)) (hl : IsLindblad g) :
    rate g ≤ diamond g ∧ frobenius (canonicalD g) ≤ diamond g / Real.sqrt 2 := by sorry

end LindbladTolerant.Testing
