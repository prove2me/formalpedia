-- Prove2me | Theorems.Thm_GL2QFT_theorem_6_10
-- name    : GL2QFT.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:22:47.507899+00:00
-- url     : https://prove2.me/theorems/15b80116-e827-4a1a-8970-e6cd447f50b6
-- title:
--   Theorem 6.10 — uniform circuits for the Gauss phase $\Gamma_q$
-- statement:
--   On the multiplicative domain of the tagged register (the zero sentinel $|0\rangle_+$ and the character labels $|\alpha\rangle_\times$), let
--   $$\Gamma_q|\alpha\rangle=\begin{cases}|0\rangle,&\alpha=0,\\-|1\rangle,&\alpha=1,\\\dfrac{g_q(\alpha)}{\sqrt q}|\alpha\rangle,&\alpha\in X_q\setminus\{1\},\end{cases}$$
--   where "$\alpha=0$" is the zero sentinel, "$\alpha=1$" the trivial character and $g_q$ the Gauss sum (265). There is a uniform family of $\{H,S,T,X,\mathrm{CNOT}\}$ circuits of size $\mathrm{poly}(\log q,\log 1/\varepsilon)$ that implements $\Gamma_q$ to operator-norm error $\varepsilon$ with clean ancillas.
--
--   The Gauss phase supplies the phases $\zeta_{\alpha,\beta}$ of the A-matrix (127) and the phase gate $D_\gamma$ of §6.5.
--
--   Differences from the source:
--   - encoding: for every $\varepsilon>0$, error $\varepsilon$, size $\mathrm{poly}(\log q,\log 1/\varepsilon)$ → for every $k$, error $2^{-k}$, size $\le c(\lfloor\log_2 q\rfloor+k+2)^c$; reason: $k=\lceil\log_2(1/\varepsilon)\rceil$, equivalent
--   - generalization: "a circuit of size …" → a uniform family printed by one polynomial-time map from $(D,1^k)$; reason: the uniform statement implies the stated existence, and the proof composes the uniform circuits of Lemma 6.8
--   - reading: an unnamed set of elementary gates → circuits over $\{H,S,T,X,\mathrm{CNOT}\}$; reason: the stronger reading, equivalent up to a $\mathrm{polylog}(1/\varepsilon)$ factor
--   - encoding: operator-norm error → $\|UV_{\mathrm{in}}\psi-V_{\mathrm{out}}\Gamma_q\psi\|_2\le2^{-k}\|\psi\|_2$ with zero-padded ancillas, no global phase, on the multiplicative domain of the tagged register; reason: the convention of Lemma 6.8 and the register of §6.4.1
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 6.10, eq. (122), p.42 (PDF p.43)

import Definitions.Def_GL2QFT_Uniform

open Classical

namespace GL2QFT

open FieldData

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 6.10** (Gauss phase), p.42 (PDF
p.43): "For every `ε > 0`, a circuit of size `poly(log q, log(1/ε))` implements, to operator-norm
error at most `ε`, the map `Γ_q|α⟩ = |0⟩` if `α = 0`; `−|1⟩` if `α = 1`; `(g_q(α)/√q)|α⟩` if
`α ∈ X_q ∖ {1}` (122)."

On the multiplicative domain of the tagged register (`Option Lab`, code `tagCode ∘ xEmb`):
`none` is the zero sentinel `|0⟩₊` ("`α = 0`"), `some 0` is the trivial character ("`α = 1`") and
`some α`, `α ≠ 0`, a nontrivial character. The family is uniform in `(D, ε)`. -/
theorem theorem_6_10 :
    UniformlyImplementsOn (fun _ => True) (X := fun D => Option D.Lab) (Y := fun D => Option D.Lab)
      (inW := fun D => (D.r + 1) * D.labW) (outW := fun D => (D.r + 1) * D.labW)
      (fun D c => D.tagCode (D.xEmb c)) (fun D c => D.tagCode (D.xEmb c))
      (fun D => Matrix.diagonal fun c =>
        match c with
        | none => 1
        | some α => if α = 0 then -1 else D.gauss α * isqrt D.q) := by sorry

end GL2QFT
