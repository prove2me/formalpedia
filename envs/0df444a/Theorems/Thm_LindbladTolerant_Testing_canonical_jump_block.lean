-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_canonical_jump_block
-- name    : LindbladTolerant.Testing.canonical_jump_block
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:58:14.625038+00:00
-- url     : https://prove2.me/theorems/bfac0e97-71c3-4a8f-a923-4f246aab1ab3
-- title:
--   Lemma 2.3 — Canonical jump block
-- statement:
--   Let $n\ge1$, $d=2^n$, and let $\mathcal L$ be a time-independent $n$-qubit Lindblad generator. All jump representations below use finite traceless jump families and a Hermitian Hamiltonian. Write $C$ for the jump block, $A=\sum_aL_a^\dagger L_a$, $\mathcal D$ for the canonical dissipator, and $\Gamma=\operatorname{Tr}C$. When $\Gamma>0$, put $\sigma=C/\Gamma$, $\sigma_R=\operatorname{Tr}_S\sigma$, and $h(\sigma)=\operatorname{Tr}(\sigma^2)+(d\operatorname{Tr}(\sigma_R^2)-1)/2$.
--
--   With $\Pi=I-|\Phi\rangle\langle\Phi|$ for the normalized maximally entangled vector and $J$ the normalized Choi map,
--   $$C=\Pi J(\mathcal L)\Pi.$$
--   Moreover, $C,A,\mathcal D,\Gamma$ agree with the quantities computed from $\mathcal L$ alone. Any two traceless representations of the same generator give identical values of all four quantities.
--
--   This makes the dissipative strength and jump state independent of the chosen jump representation.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Lemma 2.3, p.12, PDF p.12; proof continues p.13, PDF p.13

import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem canonical_jump_block {n : ℕ} (hn : 1 ≤ n) (r : LindbladRepresentation n) :
    representationC r = orthogonalProjector * choi (generator r) * orthogonalProjector ∧
    representationC r = canonicalC (generator r) ∧
    representationA r = canonicalA (generator r) ∧
    representationD r = canonicalD (generator r) ∧
    (representationC r).trace.re = rate (generator r) ∧
    (∀ s : LindbladRepresentation n, generator s = generator r →
      representationC s = representationC r ∧ representationA s = representationA r ∧
      representationD s = representationD r ∧
      (representationC s).trace.re = (representationC r).trace.re) := by sorry

end LindbladTolerant.Testing
