-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_distance_from_hamiltonian
-- name    : LindbladTolerant.Testing.distance_from_hamiltonian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:57:44.133644+00:00
-- url     : https://prove2.me/theorems/ae8c0946-50fd-4d6d-84ad-5ea6318e3d14
-- title:
--   Lemma 2.7 — Distance from Hamiltonian generators
-- statement:
--   Let $n\ge1$, $d=2^n$, and let $\mathcal L$ be a time-independent $n$-qubit Lindblad generator. All jump representations below use finite traceless jump families and a Hermitian Hamiltonian. Write $C$ for the jump block, $A=\sum_aL_a^\dagger L_a$, $\mathcal D$ for the canonical dissipator, and $\Gamma=\operatorname{Tr}C$. When $\Gamma>0$, put $\sigma=C/\Gamma$, $\sigma_R=\operatorname{Tr}_S\sigma$, and $h(\sigma)=\operatorname{Tr}(\sigma^2)+(d\operatorname{Tr}(\sigma_R^2)-1)/2$.
--
--   For any chosen traceless representation $\mathcal L=-i[H,\cdot]+\mathcal D$,
--   $$\|\mathcal D\|_F=\min_{K=K^\dagger}\|\mathcal L+i[K,\cdot]\|_F.$$
--   The minimum is attained precisely for $K-H=aI$ with $a\in\mathbb R$. In particular,
--   $$\|\mathcal D\|_F=0\quad\Longleftrightarrow\quad\mathcal L=-i[K,\cdot]\text{ for some Hermitian }K.$$
--   This identifies the canonical dissipative strength as the actual distance from Hamiltonian dynamics, retaining both the minimizer characterization and the zero-strength equivalence.
--
--   **Formalization Note** The attained minimum is expressed by a lower bound for every Hermitian candidate and an attaining candidate, rather than a totalized real infimum.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
--   - encoding: a minimum over Hermitian matrices → a lower bound for every Hermitian matrix, an attaining Hermitian matrix, and the full minimizer iff; reason: this is the definition of an attained minimum and retains every source clause
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Lemma 2.7, p.14, PDF p.14, Eq.(35)

import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem distance_from_hamiltonian {n : ℕ} (hn : 1 ≤ n) (r : LindbladRepresentation n) :
    (∀ K : Op (Qubits n), K.IsHermitian →
      frobenius (canonicalD (generator r)) ≤ frobenius (generator r - hamiltonianGenerator K)) ∧
    (∃ K : Op (Qubits n), K.IsHermitian ∧
      frobenius (generator r - hamiltonianGenerator K) = frobenius (canonicalD (generator r))) ∧
    (∀ K : Op (Qubits n), K.IsHermitian →
      (frobenius (generator r - hamiltonianGenerator K) = frobenius (canonicalD (generator r)) ↔
        ∃ a : ℝ, K - r.hamiltonian = (a : ℂ) • (1 : Op (Qubits n)))) ∧
    (frobenius (canonicalD (generator r)) = 0 ↔
      ∃ K : Op (Qubits n), K.IsHermitian ∧ generator r = hamiltonianGenerator K) := by sorry

end LindbladTolerant.Testing
