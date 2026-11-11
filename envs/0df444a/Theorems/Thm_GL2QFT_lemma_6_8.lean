-- Prove2me | Theorems.Thm_GL2QFT_lemma_6_8
-- name    : GL2QFT.lemma_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:04.334823+00:00
-- url     : https://prove2.me/theorems/ed536a20-34c8-4911-924c-eee58c167489
-- title:
--   Lemma 6.8 — uniform circuits for $\mathfrak F_+$, $\mathfrak F_\times$, $\exp_g$ and $\log_g$ on the tagged field register
-- statement:
--   On the tagged field register of §6.4.1, write $|a\rangle_+$ for $a\in\mathbb F_q$ in the polynomial basis and $|g^d\rangle_\times$ for a nonzero element stored by its exponent $d$; $|0\rangle_+$ is the zero sentinel. Each of the following four maps has a uniform family of $\{H,S,T,X,\mathrm{CNOT}\}$ circuits of size $\mathrm{poly}(\log q,\log 1/\varepsilon)$. Each circuit implements its map to operator-norm error $\varepsilon$ with all ancillary registers returned to zero.
--   1. The additive transform (119): $\mathfrak F_+|x\rangle_+=\frac{1}{\sqrt q}\sum_{y\in\mathbb F_q}\psi_x(y)|y\rangle_+$.
--   2. The multiplicative transform (120): $\mathfrak F_\times|a\rangle_\times=\frac{1}{\sqrt{q-1}}\sum_{\alpha\in X_q}\chi_\alpha(a)|\alpha\rangle_\times$ for $a\in\mathbb F_q^*$, and $\mathfrak F_\times|0\rangle_+=|0\rangle_+$.
--   3. The conversion (117): $\exp_g|g^d\rangle_\times=|g^d\rangle_+$, $|0\rangle_+\mapsto|0\rangle_+$.
--   4. The conversion (118): $\log_g|a\rangle_+=|a\rangle_\times$ for $a\neq0$, $|0\rangle_+\mapsto|0\rangle_+$.
--
--   These field transforms are the building blocks of the circuits for $\mathfrak F_B$ (Theorem 6.13), the Gauss phase (Theorem 6.10) and the torus circuit of §6.5.
--
--   **Formalization Note** Each map is required on its stated domain: the whole additive part for $\mathfrak F_+$ and $\log_g$, and $\{|0\rangle_+\}\cup\{|g^d\rangle_\times\}$ for $\mathfrak F_\times$ and $\exp_g$. The paper only says that the maps "are extended to mutually inverse unitaries on the tagged work register", without specifying the extension.
--
--   Differences from the source:
--   - encoding: for every $\varepsilon>0$, error $\varepsilon$, size $\mathrm{poly}(\log q,\log 1/\varepsilon)$ → for every $k$, error $2^{-k}$, size $\le c(\lfloor\log_2 q\rfloor+k+2)^c$; reason: $k=\lceil\log_2(1/\varepsilon)\rceil$, equivalent
--   - reading: "uniform quantum circuits" → one polynomial-time map $f$ from $(D,1^k)$ to each circuit, uniform jointly in $(D,\varepsilon)$; reason: Remark 6.3 makes uniformity relative to $D$, and joint uniformity is the stronger reading
--   - reading: an unnamed set of elementary gates → circuits over $\{H,S,T,X,\mathrm{CNOT}\}$; reason: the stronger reading, equivalent up to a $\mathrm{polylog}(1/\varepsilon)$ factor by Solovay–Kitaev
--   - encoding: the tagged register with a suppressed regime flag → the sum type $\mathbb F_q\sqcup\mathbb Z/(q-1)\mathbb Z$ with a fixed injective code; each map required on its stated domain; reason: the paper's register made explicit; the unspecified unitary extensions are not part of the claim
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Lemma 6.8 with eqs. (117)–(120), p.41 (PDF p.42)

import Definitions.Def_GL2QFT_Uniform

open Classical

namespace GL2QFT

open FieldData

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Lemma 6.8**, p.41 (PDF p.42): "For every
`ε > 0`, there are uniform quantum circuits of size `poly(log q, log(1/ε))` which, with all ancillary
registers returned to zero, implement to operator-norm error at most `ε` the transforms
`𝔉₊|x⟩₊ = (1/√q) Σ_{y∈F_q} ψ_x(y)|y⟩₊` (119),
`𝔉×|a⟩× = (1/√(q−1)) Σ_{α∈X_q} χ_α(a)|α⟩×`, `a ∈ F*_q` (120),
as well as the conversion maps Equation (117) and Equation (118). The multiplicative transform is
defined to fix `|0⟩₊`."

The registers are the tagged register of §6.4.1 (`TagReg`, code `tagCode`): `|a⟩₊ = inl a`,
`|g^d⟩× = inr d`; the multiplicative domain is `Option Lab` (`xEmb`: `none = |0⟩₊`). The four
clauses are, in order:
1. `𝔉₊` (119) on `|x⟩₊`, `ψ_x(y) = ψ(xy)`;
2. `𝔉×` (120) on `|g^d⟩×` (`a = g^d`), fixing `|0⟩₊`;
3. `exp_g` (117): `|g^d⟩× ↦ |g^d⟩₊`, `|0⟩₊ ↦ |0⟩₊`;
4. `log_g` (118): `|a⟩₊ ↦ |a⟩×` (`a ≠ 0`, the exponent `d` with `g^d = a`), `|0⟩₊ ↦ |0⟩₊`. -/
theorem lemma_6_8 :
    UniformlyImplementsOn (fun _ => True) (X := fun D => D.Fq) (Y := fun D => D.Fq)
      (inW := fun D => (D.r + 1) * D.labW) (outW := fun D => (D.r + 1) * D.labW)
      (fun D a => D.tagCode (.inl a)) (fun D a => D.tagCode (.inl a))
      (fun D => fun y x => isqrt D.q * D.psi (x * y)) ∧
    UniformlyImplementsOn (fun _ => True) (X := fun D => Option D.Lab) (Y := fun D => Option D.Lab)
      (inW := fun D => (D.r + 1) * D.labW) (outW := fun D => (D.r + 1) * D.labW)
      (fun D c => D.tagCode (D.xEmb c)) (fun D c => D.tagCode (D.xEmb c))
      (fun D => fun out inp =>
        match out, inp with
        | none, none => 1
        | some α, some d => isqrt (D.q - 1) * D.chi α (D.gen ^ d.val)
        | _, _ => 0) ∧
    UniformlyImplementsOn (fun _ => True) (X := fun D => Option D.Lab) (Y := fun D => D.Fq)
      (inW := fun D => (D.r + 1) * D.labW) (outW := fun D => (D.r + 1) * D.labW)
      (fun D c => D.tagCode (D.xEmb c)) (fun D a => D.tagCode (.inl a))
      (fun D => fun y inp =>
        match inp with
        | none => if y = 0 then 1 else 0
        | some d => if y = D.gen ^ d.val then 1 else 0) ∧
    UniformlyImplementsOn (fun _ => True) (X := fun D => D.Fq) (Y := fun D => Option D.Lab)
      (inW := fun D => (D.r + 1) * D.labW) (outW := fun D => (D.r + 1) * D.labW)
      (fun D a => D.tagCode (.inl a)) (fun D c => D.tagCode (D.xEmb c))
      (fun D => fun out a =>
        match out with
        | none => if a = 0 then 1 else 0
        | some d => if a ≠ 0 ∧ D.gen ^ d.val = a then 1 else 0) := by sorry

end GL2QFT
