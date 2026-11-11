-- Prove2me | Theorems.Thm_GL2QFT_theorem_6_34
-- name    : GL2QFT.theorem_6_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:04.835203+00:00
-- url     : https://prove2.me/theorems/7658fd97-f9b7-4f04-b9f6-4682cdd7b485
-- title:
--   Theorem 6.34 — a uniform circuit for the hard block $A_\gamma$, coherent in $\gamma$ ($q>2$)
-- statement:
--   Assume $q>2$, the standing assumption of §6.5. Let $A_\gamma$ be the $q\times q$ block (144)–(145) of the A-matrix, mapping the source states $|c_\infty\rangle,|c_\alpha\rangle$ to combinations of $|\pi_\theta\rangle$, $|I_{\delta,\eta}\rangle$, $|\mathrm{St}_\delta\rangle$. There is a uniform family of $\{H,S,T,X,\mathrm{CNOT}\}$ circuits of size $\mathrm{poly}(\log q,\log 1/\varepsilon)$, with $\gamma$ as an input register, that maps $|\gamma\rangle|c\rangle|0_{\mathrm{work}}\rangle$ to $|\gamma\rangle(A_\gamma|c\rangle)|0_{\mathrm{work}}\rangle$ to operator-norm error $\varepsilon$ on the clean-work source space $\mathrm{span}\{|\gamma\rangle|c_\infty\rangle,|\gamma\rangle|c_\alpha\rangle\}$.
--
--   This block is the only one of the A-matrix whose size grows with $q$; its efficient implementation, coherent in $\gamma$, avoids iterating over the $q-1$ values of $\gamma$ (Theorem 6.14).
--
--   **Formalization Note** The source register uses the identification $|c_\infty\rangle\leftrightarrow|0\rangle$, $|c_\alpha\rangle\leftrightarrow|\alpha\rangle$ of p.46. For $q\le2$ nothing is asserted; for $q=2$ the block is the constant rotation (147).
--
--   Differences from the source:
--   - reading: $A_\gamma$, the block of (70) → the block given by the displayed formulas (144)–(145); reason: the paper states that (144)–(145) are its entries ("These coefficients follow from Equation (70)"); its columns were checked orthonormal numerically at $q=3,5,7$
--   - encoding: for every $\varepsilon>0$, error $\varepsilon$, size $\mathrm{poly}(\log q,\log 1/\varepsilon)$ → for every $k$, error $2^{-k}$, size $\le c(\lfloor\log_2 q\rfloor+k+2)^c$; reason: $k=\lceil\log_2(1/\varepsilon)\rceil$, equivalent
--   - reading: "uniform implementation" → one polynomial-time map from $(D,1^k)$, uniform jointly in $(D,\varepsilon)$; reason: Remark 6.3, the stronger reading
--   - reading: an unnamed set of elementary gates → circuits over $\{H,S,T,X,\mathrm{CNOT}\}$; reason: the stronger reading, equivalent up to a $\mathrm{polylog}(1/\varepsilon)$ factor
--   - encoding: "the circuit for $A_\gamma$ in Figure 14 has a uniform implementation" → an implementation of $A_\gamma$ exists; reason: Figure 14 is the proof's construction, and the claim about $A_\gamma$ is the existence of such a circuit
--   - encoding: "coherent in $\gamma$" → $\gamma$ is an input register and the target is $\sum_\gamma|\gamma\rangle\langle\gamma|\otimes A_\gamma$; reason: the meaning of coherence in $\gamma$
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 6.34 eq. (168), p.55 (PDF p.56); Remark 6.15 p.48; eqs. (140)–(145) p.46

import Definitions.Def_GL2QFT_Uniform
import Definitions.Def_GL2QFT_AGamma

open Classical

namespace GL2QFT

open FieldData

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 6.34** (Efficient hard A-block),
p.55 (PDF p.56): "For every `ε > 0`, the circuit for `A_γ` in Figure 14 has a uniform implementation
of size `poly(log q, log 1/ε)` (168) whose action on the clean-work source space is within
operator-norm error `ε` of `A_γ`. The implementation is coherent in `γ`."

Under the standing assumption `q > 2` of §6.5 (Remark 6.15, p.48: "for the remainder of this
subsection we may assume that `q > 2`"), one uniform family maps `|γ⟩|c⟩|0⟩` to
`|γ⟩(A_γ|c⟩)|0⟩` to operator-norm error `2^{−k}`, with `γ` an input register (coherent in `γ`),
`c ∈ {c_∞, c_α}` the source register (`gammaInCode`: `|c_∞⟩ ↔ |0⟩₊`, `|c_α⟩ ↔ |α⟩×`) and the output
`(γ, μ)` coded by `gammaIrrCode`; `A_γ` is the block (144)–(145) (`FieldData.AGamma`). -/
theorem theorem_6_34 :
    UniformlyImplementsOn (fun D => 2 < D.q) (X := fun D => D.Lab × Option D.Lab)
      (Y := fun D => D.Lab × D.Irr)
      (inW := fun D => 1 * D.labW + (D.r + 1) * D.labW) (outW := fun D => 4 * D.labW)
      (fun D => D.gammaInCode) (fun D => D.gammaIrrCode)
      (fun D => fun out inp => if out.1 = inp.1 then D.AGamma inp.1 out.2 inp.2 else 0) := by sorry

end GL2QFT
