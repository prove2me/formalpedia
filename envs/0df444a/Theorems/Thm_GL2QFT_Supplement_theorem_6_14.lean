-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_6_14
-- name    : GL2QFT.Supplement.theorem_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:43:17.593669+00:00
-- url     : https://prove2.me/theorems/4ef707ca-154e-4a08-8fdd-3229d6cc16b1
-- title:
--   Theorem 6.14 — the total A-matrix for $B<\mathrm{GL}_2(\mathbb F_q)$ has a uniform $\mathrm{poly}(\log q,\log 1/\varepsilon)$ implementation
-- statement:
--   For every prime power $q$ (every field data $D$) and every $\varepsilon>0$, the total A-matrix of the Mackey circuit for $B<\mathrm{GL}_2(\mathbb F_q)$,
--   $$A=\sum_{\lambda,\tilde\lambda\in\widehat B}|\lambda\rangle\langle\lambda|\otimes A_{\lambda,\tilde\lambda}\otimes|\tilde\lambda\rangle\langle\tilde\lambda| ,$$
--   with blocks $A_{\lambda,\tilde\lambda}$ given by (70) for the data $\Omega=\{e,w\}$, $H_w=T$ and the untwisting (126), mapping the registers $(\lambda,\kappa,\omega,\tilde\lambda)$, $(\kappa,\omega)\in K_{\lambda,\tilde\lambda}$, to $(\lambda,\mu,\tilde\lambda)$, has an implementation to operator-norm error at most $\varepsilon$ using $\mathrm{poly}(\log q,\log(1/\varepsilon))$ gates.
--
--   Precisely: there are a constant $c$, a polynomial-time map from (the code of $D$, $k$) to a $\{H,S,T,X,\mathrm{CNOT}\}$ circuit with clean ancillas and at most $c(\lfloor\log_2q\rfloor+k+2)^c$ gates, whose action on the encoded inputs is within operator-norm error $2^{-k}$ of $A$.
--
--   The theorem supplies the last component of the Mackey circuit in the proof of Theorem 6.1; the only block whose size grows with $q$ is $A_{\rho_\gamma,\rho_\gamma}=A_\gamma$ (Theorem 6.34).
--
--   **Formalization Note** The blocks are computed from (70); their agreement with (128)–(145) is the paper's computation (checked numerically for $q=3,5,7$).
--
--   Differences from the source:
--   - reading: "has an implementation … using $\mathrm{poly}(\log q,\log(1/\varepsilon))$ gates" → one uniform family (`UniformlyImplementsOn`): size $\le c(\lfloor\log_2q\rfloor+k+2)^c$, error $2^{-k}$, gate set $\{H,S,T,X,\mathrm{CNOT}\}$, clean ancillas, no global phase; reason: the base mission's reading of $\mathrm{poly}(\log q,\log 1/\varepsilon)$ in Theorems 6.1, 6.13 and 6.34; the paper's proof gives a uniform construction
--   - encoding: the registers $(\lambda,\kappa,\omega,\tilde\lambda)$ on the multiplicity space $\mathbb C[K_{\lambda,\tilde\lambda}]$ → the domain of valid labels, $\kappa=\chi_{a,b}$ for $\omega=w$ stored as a $B$-label, fixed binary codes of label fields; reason: the paper fixes no code; the operator is defined on the multiplicity spaces
--   - encoding: $[G:B]$, $[B:H_\omega]$ in (70) → the values $q+1$, $1$, $q$; reason: $|G/B|=|\mathbb P^1(\mathbb F_q)|$ and $|B/T|=|U|=q$
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 6.14, p.47 (PDF p.48); Definition 5.3 eq. (70) p.30; §6.4.3–6.4.4 pp.44–46

import Definitions.Def_GL2QFT_Supplement_TotalA

open Classical

namespace GL2QFT

namespace Supplement

open FieldData TotalA

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 6.14 (Efficient implementation of
the total A-matrix)**, p.47 (PDF p.48): "For every `ε > 0`, the total A-matrix in the Mackey circuit
for `B < GL₂(F_q)` has an implementation to operator-norm error at most `ε` using
`poly(log q, log(1/ε))` gates."

For every field data `D` (every prime power `q`), the total A-matrix
`A = Σ_{λ,λ̃ ∈ B̂} |λ⟩⟨λ| ⊗ A_{λ,λ̃} ⊗ |λ̃⟩⟨λ̃|` with blocks (70) (`totalA`), from the registers
`(λ, κ, ω, λ̃)` with `(κ, ω) ∈ K_{λ,λ̃}` to the registers `(λ, μ, λ̃)`, is implemented by one uniform
family of `{H, S, T, X, CNOT}` circuits with clean ancillas, of size `≤ c(⌊log₂ q⌋ + k + 2)^c`, to
operator-norm error `2^{−k}` (`UniformlyImplementsOn`, the base mission's reading of
`poly(log q, log(1/ε))`). -/
theorem theorem_6_14 :
    UniformlyImplementsOn (fun _ => True) (X := fun D => InReg D) (Y := fun D => OutReg D)
      (inW := fun D => 10 * D.labW) (outW := fun D => 9 * D.labW)
      (fun D => inCodeA D) (fun D => outCodeA D) (fun D => totalA D) := by sorry

end Supplement

end GL2QFT
