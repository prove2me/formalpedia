-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_rate_state_identity
-- name    : LindbladTolerant.Testing.rate_state_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:57:43.650799+00:00
-- url     : https://prove2.me/theorems/ed2b9b3b-ac11-43b2-83c5-ee29165b7871
-- title:
--   Lemma 2.6 — Rate–state identity
-- statement:
--   Let $n\ge1$, $d=2^n$, and let $\mathcal L$ be a time-independent $n$-qubit Lindblad generator. All jump representations below use finite traceless jump families and a Hermitian Hamiltonian. Write $C$ for the jump block, $A=\sum_aL_a^\dagger L_a$, $\mathcal D$ for the canonical dissipator, and $\Gamma=\operatorname{Tr}C$. When $\Gamma>0$, put $\sigma=C/\Gamma$, $\sigma_R=\operatorname{Tr}_S\sigma$, and $h(\sigma)=\operatorname{Tr}(\sigma^2)+(d\operatorname{Tr}(\sigma_R^2)-1)/2$.
--
--   For $\Gamma>0$,
--   $$\|\mathcal D\|_F=\Gamma\sqrt{1+h(\sigma)}.$$
--   This identity separates dissipative strength into its total rate and the shape-dependent functional. Positive rate already excludes the zero dissipator; no extra nonzero assumption is imposed.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
--   - encoding: the jump state of a nonzero canonical dissipator → jumpState of a Lindblad generator with a proof that its canonical rate is positive; reason: every canonical dissipator is realized by such a generator; in the traceless Lindblad class nonzero dissipator is equivalent to positive rate, and the proof argument prevents division at zero
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Lemma 2.6, p.13, PDF p.13; proof continues p.14, PDF p.14

import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem rate_state_identity {n : ℕ} (hn : 1 ≤ n)
    (g : Super (Qubits n) (Qubits n)) (hl : IsLindblad g) (hp : 0 < rate g) :
    frobenius (canonicalD g) = rate g * Real.sqrt (1 + functional (jumpState g hp)) := by sorry

end LindbladTolerant.Testing
