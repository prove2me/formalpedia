-- Prove2me | Theorems.Thm_GL2QFT_theorem_6_1
-- name    : GL2QFT.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:15.030092+00:00
-- url     : https://prove2.me/theorems/b4a95143-b382-476c-ab11-92664b76cc6d
-- title:
--   Theorem 6.1 — a uniform circuit of size $\mathrm{poly}(\log q,\log 1/\varepsilon)$ implementing the QFT of $\mathrm{GL}_2(\mathbb F_q)$
-- statement:
--   Let $q=p^r$ be any prime power, given by field data $D$: polynomial-basis models of $\mathbb F_q\subset\mathbb F_{q^2}$ and a primitive element $h\in\mathbb F_{q^2}^*$ (Remark 6.3). Let $\mathfrak F_G$ be the quantum Fourier transform (22) of $G=\mathrm{GL}_2(\mathbb F_q)$ in the paper's representatives and Gelfand–Tsetlin bases of §6.1–6.2, with all phases equal to one.
--
--   Then there are a polynomial-time computable map $f$ and a constant $c$ with the following property. For every $D$ and every $k\in\mathbb N$, $f$ prints from the binary code of $D$ and $1^k$ a circuit $U$ of at most $c(\lfloor\log_2q\rfloor+k+2)^c$ gates from $\{H,S,T,X,\mathrm{CNOT}\}$. This circuit implements $\mathfrak F_G$ to operator-norm error $2^{-k}$ with clean ancillas:
--   $$\bigl\|U V_{\mathrm{in}}\psi-V_{\mathrm{out}}\mathfrak F_G\psi\bigr\|_2\le 2^{-k}\|\psi\|_2\qquad(\psi\in\mathbb C[G]).$$
--   Here $V_{\mathrm{in}}$ writes $g$ by its four entries in the polynomial basis and $V_{\mathrm{out}}$ writes the label $(\mu,i,j)$, both padded with $|0\rangle$. Equivalently, for every $\varepsilon>0$ there is a uniform circuit of size $\mathrm{poly}(\log q,\log 1/\varepsilon)$ implementing the QFT of $\mathrm{GL}_2(\mathbb F_q)$ to operator-norm error $\varepsilon$.
--
--   This is the first polylogarithmic-size QFT for an infinite family of non-abelian groups of Lie type.
--
--   Differences from the source:
--   - encoding: for every $\varepsilon>0$, error $\varepsilon$, size $\mathrm{poly}(\log q,\log 1/\varepsilon)$ → for every $k$, error $2^{-k}$, size $\le c(\lfloor\log_2 q\rfloor+k+2)^c$ with $c$ fixed before $D$ and $k$; reason: $k=\lceil\log_2(1/\varepsilon)\rceil$ gives error $\le\varepsilon$ and the same size class, and conversely
--   - reading: "uniform quantum circuit", relative to $D$ (Remark 6.3) → one polynomial-time map $f$ prints the wire count and the instruction list from the binary code of $D$ and $1^k$; reason: uniformity relative to the supplied data, joint in $(D,\varepsilon)$, the stronger reading
--   - reading: an unnamed set of elementary gates → circuits over $\{H,S,T,X,\mathrm{CNOT}\}$; reason: the stronger reading, equivalent up to a $\mathrm{polylog}(1/\varepsilon)$ factor by Solovay–Kitaev
--   - reading: "the QFT of $\mathrm{GL}_2(\mathbb F_q)$" → $\mathfrak F_G$ of (22) in the explicit models (87)–(100) and bases (108), (110)–(112), with the representative $\alpha\prec\beta$ of $I_{\alpha,\beta}$ for the exponent order and the smaller-exponent representative of each orbit $\{\theta,\theta^q\}$; reason: a Fourier transform is fixed only after the bases (Proposition 2.7, "Throughout this paper, $\mathfrak F_G$ denotes the choice in Equation (22)"); §6.2 fixes the bases; "Fix a total order $\prec$" (p.44) leaves the order free and the exponent order is the one the proof computes
--   - encoding: $\pi_\theta$ specified on $B$ and $w'$ → extended to $\mathrm{GL}_2(\mathbb F_q)$ through $g=\begin{pmatrix}1&a/c\\0&1\end{pmatrix}w'\begin{pmatrix}-c&-d\\0&-\det g/c\end{pmatrix}$; reason: a representation is determined by these values; the factorization is the paper's Bruhat decomposition written out
--   - encoding: operator-norm error → $\|UV_{\mathrm{in}}\psi-V_{\mathrm{out}}\mathfrak F_G\psi\|_2\le2^{-k}\|\psi\|_2$ with zero-padded ancillas and no global phase; reason: the convention of Lemma 6.8 ("with all ancillary registers returned to zero")
--   - encoding: the input and output registers → fixed injective bit codes (entries in the polynomial basis; five label fields); reason: the paper leaves the layout implicit (Remark 2.3); layouts differ by reversible polynomial-time relabelings
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 6.1, p.34 (PDF p.35) = Theorem 1.2, p.5 (PDF p.6); Remark 6.3 p.34; proof p.47 (PDF p.48)

import Definitions.Def_GL2QFT_Uniform

open Classical

namespace GL2QFT

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 6.1** (QFT for `GL₂(F_q)`), p.34
(PDF p.35), restated as Theorem 1.2, p.5: "For every `ε > 0`, there exists a uniform quantum circuit
of size `poly(log q, log 1/ε)` that implements the QFT of `GL₂(F_q)` to operator-norm error at most
`ε`."

For every field data `D` (every prime `p`, every `r ≥ 1`, `q = p^r`, every polynomial-basis model
of `F_q ⊂ F_{q²}` and every primitive `h ∈ F*_{q²}`, Remark 6.3) and every `k`, one polynomial-time
map prints, from the binary code of `D` and `1^k`, a `{H, S, T, X, CNOT}` circuit of size
`≤ c · (⌊log₂ q⌋ + k + 2)^c` that implements the Fourier transform `F_G` of (22) in the paper's
explicit Gelfand–Tsetlin bases (`FieldData.qftGL2`) to operator-norm error `2^{−k}` with clean
ancillas, reading `g` through `inCode` (entries in the polynomial basis) and writing `(μ, i, j)`
through `outCode`. -/
theorem theorem_6_1 :
    UniformlyImplementsOn (fun _ => True) (X := fun D => D.G) (Y := fun D => D.OutLabel)
      (inW := fun D => 4 * D.r * D.digitW) (outW := fun D => 5 * D.labW)
      (fun D => D.inCode) (fun D => D.outCode) (fun D => D.qftGL2) := by sorry

end GL2QFT
