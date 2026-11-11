-- Prove2me | Theorems.Thm_GL2QFT_theorem_6_13
-- name    : GL2QFT.theorem_6_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:19.552709+00:00
-- url     : https://prove2.me/theorems/a9f55939-ae1b-48b8-b0ef-b3fde292266c
-- title:
--   Theorem 6.13 — a uniform circuit of size $\mathrm{poly}(\log q,\log 1/\varepsilon)$ for $\mathfrak F_B$
-- statement:
--   Let $B=\left\{\begin{pmatrix}a&b\\0&d\end{pmatrix}:a,d\in\mathbb F_q^*,\ b\in\mathbb F_q\right\}$ be the Borel subgroup of $\mathrm{GL}_2(\mathbb F_q)$ and $\mathfrak F_B$ its Fourier transform (22) in the bases fixed in §6.1–6.2: the characters $\chi_{\alpha,\beta}$ and the representations $\rho_\gamma$ in the multiplicative Fourier basis. Then there are a polynomial-time map $f$ and a constant $c$ with the following property. For every field data $D$ and every $k\in\mathbb N$, $f$ prints from $(D,1^k)$ a $\{H,S,T,X,\mathrm{CNOT}\}$ circuit of at most $c(\lfloor\log_2q\rfloor+k+2)^c$ gates. It maps the input registers $|a\rangle_\times|d\rangle_\times|b\rangle_+$ of $g=\begin{pmatrix}1&b\\0&1\end{pmatrix}\begin{pmatrix}a&0\\0&d\end{pmatrix}$, with clean ancillas, to the label register of $\mathfrak F_B|g\rangle$ up to operator-norm error $2^{-k}$:
--   $$\bigl\|U V_{\mathrm{in}}\psi-V_{\mathrm{out}}\mathfrak F_B\psi\bigr\|_2\le 2^{-k}\|\psi\|_2\qquad(\psi\in\mathbb C[B]).$$
--
--   $\mathfrak F_B$ is the subgroup transform in the factorization (146) of $\mathfrak F_G$; this theorem is the first ingredient of the proof of Theorem 6.1.
--
--   **Formalization Note** $k$ stands for $\lceil\log_2(1/\varepsilon)\rceil$.
--
--   Differences from the source:
--   - encoding: for every $\varepsilon>0$, error $\varepsilon$, size $\mathrm{poly}(\log q,\log 1/\varepsilon)$ → for every $k$, error $2^{-k}$, size $\le c(\lfloor\log_2 q\rfloor+k+2)^c$; reason: $k=\lceil\log_2(1/\varepsilon)\rceil$ gives error $\le\varepsilon$ and the same size class, and conversely
--   - generalization: "there is a quantum circuit" → one polynomial-time generator $f$ prints the circuit from $(D,1^k)$; reason: the uniform statement implies the stated existence, and the proof composes uniform circuits (Lemma 6.8: "uniform quantum circuits")
--   - reading: an unnamed set of elementary gates → circuits over $\{H,S,T,X,\mathrm{CNOT}\}$; reason: the stronger reading, equivalent up to a $\mathrm{polylog}(1/\varepsilon)$ factor by Solovay–Kitaev
--   - encoding: operator-norm error with ancillas → $\|UV_{\mathrm{in}}\psi-V_{\mathrm{out}}\mathfrak F_B\psi\|_2\le 2^{-k}\|\psi\|_2$ with zero-padded ancillas and no global phase; reason: the convention of Lemma 6.8 ("with all ancillary registers returned to zero")
--   - encoding: the registers $|a,d\rangle|b\rangle$ and $|\chi^*\rangle|\lambda\rangle|\tilde\chi\rangle$ → fixed injective bit codes `bInCode`, `bOutCode`; reason: the paper leaves the layout implicit (Remark 2.3); layouts differ by reversible polynomial-time relabelings
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 6.13 and (125), p.44 (PDF p.45); §6.4.2 p.43 (registers)

import Definitions.Def_GL2QFT_Uniform

open Classical

namespace GL2QFT

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 6.13**, p.44 (PDF p.45): "For every
`ε > 0`, there is a quantum circuit of size `poly(log q, log(1/ε))` that implements the Fourier
transform `F_B` of `B = {(a b; 0 d) : a, d ∈ F*_q, b ∈ F_q}` (125) in the representation bases fixed
above, to operator-norm error at most `ε`."

`F_B` is (22) for `B` with the characters `χ_{α,β}` (87) and `ρ_γ` in the basis (108)
(`FieldData.qftB`). The input registers are `|a⟩×|d⟩×|b⟩₊` for `g = (1 b; 0 1)(a 0; 0 d)` (§6.4.2,
p.43), coded by `bInCode`; the output label `(λ, i, j)` is coded by `bOutCode`. The family is
uniform in `(D, ε)` (one polynomial-time generator, as in Theorem 6.1). -/
theorem theorem_6_13 :
    UniformlyImplementsOn (fun _ => True) (X := fun D => D.BElt) (Y := fun D => D.BOutLabel)
      (inW := fun D => (D.r + 1) * D.labW + (D.r + 1) * D.labW + (D.r + 1) * D.labW)
      (outW := fun D => 5 * D.labW)
      (fun D => D.bInCode) (fun D => D.bOutCode) (fun D => D.qftB) := by sorry

end GL2QFT
