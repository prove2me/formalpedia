-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_jump_state_locality_bounds
-- name    : LindbladTolerant.Testing.jump_state_locality_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:57:33.205971+00:00
-- url     : https://prove2.me/theorems/128bbe22-c9d3-414a-915c-353293948acd
-- title:
--   Lemma 2.10 — Locality bounds for the jump state
-- statement:
--   Let $n\ge1$, $d=2^n$, and let $\mathcal L$ be a time-independent $n$-qubit Lindblad generator. All jump representations below use finite traceless jump families and a Hermitian Hamiltonian. Write $C$ for the jump block, $A=\sum_aL_a^\dagger L_a$, $\mathcal D$ for the canonical dissipator, and $\Gamma=\operatorname{Tr}C$. When $\Gamma>0$, put $\sigma=C/\Gamma$, $\sigma_R=\operatorname{Tr}_S\sigma$, and $h(\sigma)=\operatorname{Tr}(\sigma^2)+(d\operatorname{Tr}(\sigma_R^2)-1)/2$.
--
--   Suppose $k\ge1$, the canonical dissipator admits a traceless $k$-local representation, and $\Gamma>0$. Then all three bounds hold:
--   $$\sigma_R\le\frac{2^k}{d}I,\qquad 1\le d\operatorname{Tr}(\sigma_R^2)\le2^k,\qquad 0\le h(\sigma)\le\frac{2^k+1}{2}.$$
--   These dimension-independent bounds supply the estimator's variance control and the tester's range of functional values.
--
--   **Formalization Note** The operator inequality is expressed as positive semidefiniteness of $(2^k/d)I-\sigma_R$. Locality is existential over representations and permits $k>n$.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
--   - encoding: the jump state of a nonzero canonical dissipator → jumpState of a Lindblad generator with a proof that its canonical rate is positive; reason: every canonical dissipator is realized by such a generator; in the traceless Lindblad class nonzero dissipator is equivalent to positive rate, and the proof argument prevents division at zero
--   - encoding: the operator inequality sigma_R <= (2^k/d) I → positive semidefiniteness of (2^k/d) I - sigma_R; reason: positive semidefinite order on finite Hermitian matrices has exactly this meaning
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Lemma 2.10, p.16, PDF p.16

import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem jump_state_locality_bounds {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (g : Super (Qubits n) (Qubits n)) (hl : LocalGenerator k g) (hp : 0 < rate g) :
    (((2 : ℂ)^k / (2 : ℂ)^n) • (1 : Op (Qubits n)) -
      traceSystem (jumpState g hp)).PosSemidef ∧
    1 ≤ (2 : ℝ)^n * (traceSystem (jumpState g hp) *
      traceSystem (jumpState g hp)).trace.re ∧
    (2 : ℝ)^n * (traceSystem (jumpState g hp) *
      traceSystem (jumpState g hp)).trace.re ≤ (2 : ℝ)^k ∧
    0 ≤ functional (jumpState g hp) ∧
    functional (jumpState g hp) ≤ ((2 : ℝ)^k + 1)/2 := by sorry

end LindbladTolerant.Testing
